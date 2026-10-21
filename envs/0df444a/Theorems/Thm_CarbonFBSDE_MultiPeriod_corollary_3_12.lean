-- Prove2me | Theorems.Thm_CarbonFBSDE_MultiPeriod_corollary_3_12
-- name    : CarbonFBSDE.MultiPeriod.corollary_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:31.199049+00:00
-- url     : https://prove2.me/theorems/50cb055d-1111-4c69-9409-6e6170284972
-- title:
--   Corollary 3.12, p. 23 — the parametrised one-period FBSDE with terminal Φ(·,·,𝔢), Φ ∈ 𝒦̂, has a unique value function v^Φ with properties (1)–(4)
-- statement:
--   Let Assumption 1 hold, $r\in\mathbb R$, $\tau>0$, and $\Phi\in\widehat{\mathcal K}$ with Lipschitz constant $L_\Phi$. Then for every $(t_0,p,e,\mathfrak e)\in[0,\tau)\times\mathbb R^d\times\mathbb R\times\mathbb R$ the system (3.4)–(3.5) with terminal condition $\Phi(\cdot,\cdot,\mathfrak e)$ has a solution, unique in the classes of Proposition 3.2, and there is a unique function
--   $$[0,\tau)\times\mathbb R^d\times\mathbb R\times\mathbb R\ni(t_0,p,e,\mathfrak e)\mapsto v^\Phi(t_0,p,e,\mathfrak e)=Y^{t_0,p,e,\mathfrak e}_{t_0}\in\mathbb R.$$
--   For each $\mathfrak e$ it is continuous in $(t,p,e)$, and there is $C>0$ depending only on $L$, $L_\Phi$ and $\tau$ such that:
--
--   1. $v^\Phi(t,\cdot,\cdot,\cdot)$ is $1/(l_1(\tau-t))$-Lipschitz in $e$;
--   2. $v^\Phi(t,\cdot,\cdot,\cdot)$ is $C$-Lipschitz in $p$;
--   3. for $(p,e)$, $\mathfrak e$ and any family $(p_t,e_t)\to(p,e)$ as $t\uparrow\tau$, $\Phi_-(p,e,\mathfrak e)\le\liminf_{t\to\tau}v^\Phi(t,p_t,e_t,\mathfrak e)\le\limsup_{t\to\tau}v^\Phi(t,p_t,e_t,\mathfrak e)\le\Phi_+(p,e,\mathfrak e)$ (3.47), uniformly for $p$ in compact subsets of $\mathbb R^d$;
--   4. every solution from $(t_0,p,e)$ with terminal condition $\Phi(\cdot,\cdot,\mathfrak e)$ satisfies $Y_t=v^\Phi(t,P_t,E_t,\mathfrak e)$ for $t_0\le t<\tau$, almost surely.
--
--   This is the version of Proposition 3.2 for terminal conditions carrying the extra parameter $\mathfrak e$, the emission level at the start of the period, which is how consecutive periods are linked.
--
--   **Formalization Note** "It is continuous" is read in $(t,p,e)$ for each fixed $\mathfrak e$: $\Phi$ is only measurable in $\mathfrak e$ (e.g. $\mathbf 1_{e\ge\Lambda(\mathfrak e)}$ with a discontinuous $\Lambda\in\Theta$), so joint continuity in $\mathfrak e$ fails in general; this is also the reading of Proposition 3.15 (1). $\Phi_\pm$ are the left/right versions in $e$ of $\Phi(\cdot,\cdot,\mathfrak e)$. Item 3 is stated in $\varepsilon$–$\delta$ form: for fixed $e,\mathfrak e$, a compact $K$ and $\varepsilon>0$ there is $\delta>0$ such that $\Phi_-(p,e,\mathfrak e)-\varepsilon\le v^\Phi(t,p',e',\mathfrak e)\le\Phi_+(p,e,\mathfrak e)+\varepsilon$ whenever $p\in K$, $\tau-\delta<t<\tau$, $|p'-p|<\delta$, $|e'-e|<\delta$; for a single $p$ this is equivalent to the family formulation. The constant $C$ is quantified after $d,r,L,\tau,L_\Phi$ and before everything else.
-- source:
--   Chassagneux, Chotai & Crisan, Modelling multi-period carbon markets using singular forward-backward SDEs, arXiv:2008.09044v1, p. 23, Corollary 3.12, (3.47)

import Mathlib
import Definitions.Def_CarbonFBSDE_MultiPeriod_Model

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped NNReal ENNReal Topology

namespace CarbonFBSDE.MultiPeriod

universe u

theorem corollary_3_12 (d : ℕ) (r L : ℝ) (τ : ℝ≥0) (LΦ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (B : Basis d Ω), B.Valid →
    ∀ (c : Coeffs d) (l1 l2 : ℝ), Assumption1 c L l1 l2 →
    ∀ Φ : SDEState d → ℝ → ℝ → ℝ, InKhat Φ LΦ → 0 < τ →
    (∀ t0 < τ, ∀ (p : SDEState d) (e ee : ℝ),
      (∃ P E Y Z, IsOnePeriodSol B c r (fun p e => Φ p e ee) t0 τ p e P E Y Z) ∧
      (∀ P E Y Z P' E' Y' Z', IsOnePeriodSol B c r (fun p e => Φ p e ee) t0 τ p e P E Y Z →
        IsOnePeriodSol B c r (fun p e => Φ p e ee) t0 τ p e P' E' Y' Z' →
        SolAgree B (Icc t0 τ) (Ico t0 τ) t0 τ P E Y Z P' E' Y' Z')) ∧
    ∃ v : ℝ≥0 → SDEState d → ℝ → ℝ → ℝ, IsValueFn B c r Φ τ v ∧
      -- uniqueness of v^Φ on [0, τ)
      (∀ v', IsValueFn B c r Φ τ v' → ∀ t < τ, ∀ p e ee, v' t p e ee = v t p e ee) ∧
      -- continuity in (t, p, e) for each 𝔢
      (∀ ee : ℝ, ContinuousOn (fun x : ℝ≥0 × SDEState d × ℝ => v x.1 x.2.1 x.2.2 ee)
        (Ico 0 τ ×ˢ univ)) ∧
      -- (1)
      (∀ t < τ, ∀ (p : SDEState d) (e e' ee : ℝ),
        |v t p e ee - v t p e' ee| ≤ 1 / (l1 * ((τ : ℝ) - t)) * |e - e'|) ∧
      -- (2)
      (∀ t < τ, ∀ (p p' : SDEState d) (e ee : ℝ),
        |v t p e ee - v t p' e ee| ≤ C * ‖p - p'‖) ∧
      -- (3), (3.47), uniformly for p in compact sets
      (∀ (e ee : ℝ) (K : Set (SDEState d)), IsCompact K → ∀ ε > 0, ∃ δ > 0,
        ∀ p ∈ K, ∀ (t : ℝ≥0) (p' : SDEState d) (e' : ℝ),
          (τ : ℝ) - δ < t → t < τ → ‖p' - p‖ < δ → |e' - e| < δ →
          lowerVer (fun p e => Φ p e ee) p e - ε ≤ v t p' e' ee ∧
            v t p' e' ee ≤ upperVer (fun p e => Φ p e ee) p e + ε) ∧
      -- (4)
      (∀ t0 < τ, ∀ (p : SDEState d) (e ee : ℝ) P E Y Z,
        IsOnePeriodSol B c r (fun p e => Φ p e ee) t0 τ p e P E Y Z →
        ∀ᵐ ω ∂B.Pr, ∀ t ∈ Ico t0 τ, Y t ω = v t (P t ω) (E t ω) ee) := by sorry

end CarbonFBSDE.MultiPeriod
