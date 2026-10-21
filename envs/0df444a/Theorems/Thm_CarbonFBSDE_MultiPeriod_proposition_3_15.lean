-- Prove2me | Theorems.Thm_CarbonFBSDE_MultiPeriod_proposition_3_15
-- name    : CarbonFBSDE.MultiPeriod.proposition_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:35.758143+00:00
-- url     : https://prove2.me/theorems/9e7efa6a-a670-4928-b399-eee9277b66d5
-- title:
--   Proposition 3.15, pp. 25–26 — the q-period pricing function v^q exists, with properties (1)–(5)
-- statement:
--   Let Assumption 1 hold with $r\ge0$, let $\theta\in\widehat{\mathcal K}$ with Lipschitz constant $L_\theta$, $q\ge1$, $0=T_0<T_1<\dots<T_q=T$, and $\Lambda_1,\dots,\Lambda_{q-1}\in\Theta$ with $\Lambda_k(\mathfrak e)-\mathfrak e\to+\infty$ as $\mathfrak e\to-\infty$. There exist constants $C^q_k$, depending only on $L$, $L_\theta$, $T$ and $q$, and a bounded measurable function $v^q:[0,T)\times\mathbb R^d\times\mathbb R\times\mathbb R\to\mathbb R$ such that, for $1\le k\le q$:
--
--   1. for each $\mathfrak e$, $v^q(\cdot,\cdot,\cdot,\mathfrak e)$ is continuous on $[T_{k-1},T_k)\times\mathbb R^d\times\mathbb R$;
--   2. for $t\in[T_{k-1},T_k)$, $v^q(t,\cdot,\cdot,\cdot)$ is $1/(l_1(T_k-t))$-Lipschitz in $e$;
--   3. for $t\in[T_{k-1},T_k)$, $v^q(t,\cdot,\cdot,\cdot)$ is $C^q_k$-Lipschitz in $p$;
--   4. with $\Phi^{q,k}(p,e,\mathfrak e)=v^q(T_k,p,e,e)$ if $e<\Lambda_k(\mathfrak e)$ and $1$ otherwise ($k<q$), and $\Phi^{q,q}=\theta$,
--   $$\Phi^{q,k}_-(p,e,\mathfrak e)\le\liminf_{t\uparrow T_k}v^q(t,p_t,e_t,\mathfrak e)\le\limsup_{t\uparrow T_k}v^q(t,p_t,e_t,\mathfrak e)\le\Phi^{q,k}_+(p,e,\mathfrak e)\tag{3.59}$$
--   for every family $(p_t,e_t)\to(p,e)$ as $t\uparrow T_k$;
--   5. for $(t_0,p,e,\mathfrak e)\in[T_{k-1},T_k)\times\mathbb R^d\times\mathbb R\times\mathbb R$, the system (3.4)–(3.5) on $[t_0,T_k]$ from $(p,e)$ with terminal condition $\Phi^{q,k}(\cdot,\cdot,\mathfrak e)$ has a solution, and every solution satisfies $v^q(t,P_t,E_t,\mathfrak e)=Y_t$ for $t_0\le t<T_k$, almost surely.
--
--   The function $v^q$ is the pricing function of the $q$-period market, built backwards period by period; it is the decoupling field of Theorem 2.3.
--
--   **Formalization Note** The hypotheses $r\ge0$ and $\Lambda_k(\mathfrak e)-\mathfrak e\to+\infty$ at $-\infty$ are **added**: the proof applies Corollary 3.14 at every step, which needs both (see that item). Assumption 1 is the paper's standing hypothesis. The constants $C^q_k$ are chosen after $d,r,L,L_\theta,T,q$ and before the probability space, coefficients, $\theta$, the grid and the caps. "Bounded and measurable on $[0,T)$" is stated for $v^q$ cut to $0$ for $t\ge T$. (3.59) is in $\varepsilon$-form as in Proposition 3.2. In (5), the existence of the solution is the presupposition of "where $(\dots)$ is solution to".
-- source:
--   Chassagneux, Chotai & Crisan, Modelling multi-period carbon markets using singular forward-backward SDEs, arXiv:2008.09044v1, pp. 25–26, Proposition 3.15, (3.57)–(3.59)

import Mathlib
import Definitions.Def_CarbonFBSDE_MultiPeriod_Model

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped NNReal ENNReal Topology

namespace CarbonFBSDE.MultiPeriod

universe u

theorem proposition_3_15 (d : ℕ) (r L Lθ : ℝ) (T : ℝ≥0) (q : ℕ) :
    ∃ C : ℕ → ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (B : Basis d Ω), B.Valid →
    ∀ (c : Coeffs d) (l1 l2 : ℝ), Assumption1 c L l1 l2 → 0 ≤ r →
    ∀ θ : SDEState d → ℝ → ℝ → ℝ, InKhat θ Lθ → 1 ≤ q →
    ∀ Tg : ℕ → ℝ≥0, Tg 0 = 0 → (∀ k < q, Tg k < Tg (k + 1)) → Tg q = T →
    ∀ Λ : ℕ → ℝ → ℝ, (∀ k, 1 ≤ k → k < q → InTheta (Λ k) ∧ CapUnbounded (Λ k)) →
    ∃ vq : ℝ≥0 → SDEState d → ℝ → ℝ → ℝ,
      -- bounded and measurable on [0, T) × ℝ^d × ℝ × ℝ
      (∃ M : ℝ, ∀ t < T, ∀ p e ee, |vq t p e ee| ≤ M) ∧
      Measurable (fun x : ℝ≥0 × SDEState d × ℝ × ℝ =>
        if x.1 < T then vq x.1 x.2.1 x.2.2.1 x.2.2.2 else 0) ∧
      -- (1)
      (∀ (ee : ℝ) (k : ℕ), 1 ≤ k → k ≤ q →
        ContinuousOn (fun x : ℝ≥0 × SDEState d × ℝ => vq x.1 x.2.1 x.2.2 ee)
          (Ico (Tg (k - 1)) (Tg k) ×ˢ univ)) ∧
      -- (2)
      (∀ k, 1 ≤ k → k ≤ q → ∀ t ∈ Ico (Tg (k - 1)) (Tg k), ∀ (p : SDEState d) (e e' ee : ℝ),
        |vq t p e ee - vq t p e' ee| ≤ 1 / (l1 * ((Tg k : ℝ) - t)) * |e - e'|) ∧
      -- (3)
      (∀ k, 1 ≤ k → k ≤ q → ∀ t ∈ Ico (Tg (k - 1)) (Tg k), ∀ (p p' : SDEState d) (e ee : ℝ),
        |vq t p e ee - vq t p' e ee| ≤ C k * ‖p - p'‖) ∧
      -- (4), (3.57)–(3.59)
      (∀ k, 1 ≤ k → k ≤ q → ∀ (p : SDEState d) (e ee : ℝ) (pt : ℝ≥0 → SDEState d)
        (et : ℝ≥0 → ℝ), Tendsto (fun t => (pt t, et t)) (𝓝[<] (Tg k)) (𝓝 (p, e)) →
        ∀ ε > 0, ∀ᶠ t in 𝓝[<] (Tg k),
          lowerVer (fun p e => PhiQK vq θ Λ Tg q k p e ee) p e - ε ≤ vq t (pt t) (et t) ee ∧
          vq t (pt t) (et t) ee ≤ upperVer (fun p e => PhiQK vq θ Λ Tg q k p e ee) p e + ε) ∧
      -- (5)
      (∀ k, 1 ≤ k → k ≤ q → ∀ t0 ∈ Ico (Tg (k - 1)) (Tg k), ∀ (p : SDEState d) (e ee : ℝ),
        (∃ P E Y Z, IsOnePeriodSol B c r (fun p e => PhiQK vq θ Λ Tg q k p e ee)
          t0 (Tg k) p e P E Y Z) ∧
        ∀ P E Y Z, IsOnePeriodSol B c r (fun p e => PhiQK vq θ Λ Tg q k p e ee)
          t0 (Tg k) p e P E Y Z →
          ∀ᵐ ω ∂B.Pr, ∀ t ∈ Ico t0 (Tg k), Y t ω = vq t (P t ω) (E t ω) ee) := by sorry

end CarbonFBSDE.MultiPeriod
