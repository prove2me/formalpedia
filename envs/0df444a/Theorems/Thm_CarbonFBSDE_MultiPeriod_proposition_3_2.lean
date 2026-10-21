-- Prove2me | Theorems.Thm_CarbonFBSDE_MultiPeriod_proposition_3_2
-- name    : CarbonFBSDE.MultiPeriod.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:36.335439+00:00
-- url     : https://prove2.me/theorems/4c883d31-c4eb-43dc-a035-93bef0696d84
-- title:
--   Proposition 3.2, p. 14 — the one-period singular FBSDE (3.4)–(3.5) is well posed; its value function is continuous, Lipschitz in e and p, and has the boundary behaviour (3.6)
-- statement:
--   Let Assumption 1 hold, let $r\in\mathbb R$, $\tau>0$, and let $\varphi\in\mathcal K$ with Lipschitz constant $L_\varphi$. Then:
--
--   1. For every $(t_0,p,e)\in[0,\tau)\times\mathbb R^d\times\mathbb R$ there is a solution $(P,E,Y,Z)\in\mathcal S^{2,d}_c([t_0,\tau])\times\mathcal S^{2,1}_c([t_0,\tau])\times\mathcal S^{2,1}_c([t_0,\tau))\times\mathcal H^{2,d}([t_0,\tau])$ of
--   $$dP_t=b(P_t)\,dt+\sigma(P_t)\,dW_t,\ P_{t_0}=p,\qquad dE_t=\mu(P_t,Y_t)\,dt,\ E_{t_0}=e,\qquad dY_t=rY_t\,dt+Z_t\,dW_t,$$
--   with $\mathbb P\big[\varphi_-(P_\tau,E_\tau)\le\lim_{t\uparrow\tau}Y_t\le\varphi_+(P_\tau,E_\tau)\big]=1$, and any two solutions agree.
--   2. The function $v(t_0,p,e)=Y^{t_0,p,e}_{t_0}$ on $[0,\tau)\times\mathbb R^d\times\mathbb R$ is continuous and
--      - $|v(t,p,e)-v(t,p,e')|\le\dfrac{|e-e'|}{l_1(\tau-t)}$;
--      - $|v(t,p,e)-v(t,p',e)|\le C|p-p'|$, where $C$ depends only on $L$, $\tau$ and $L_\varphi$ (and on the fixed $d$ and $r$);
--      - for $(p_t,e_t)\to(p,e)$ as $t\uparrow\tau$, $\varphi_-(p,e)\le\liminf_{t\to\tau}v(t,p_t,e_t)\le\limsup_{t\to\tau}v(t,p_t,e_t)\le\varphi_+(p,e)$.
--
--   This is the basic well-posedness result for one-period FBSDEs with a discontinuous terminal condition depending on both $P$ and $E$; every later step of the multi-period construction applies it period by period.
--
--   **Formalization Note** The constant $C$ is quantified after $d,r,L,\tau,L_\varphi$ and before the probability space, the coefficients, $l_1,l_2$ and $\varphi$. The liminf/limsup bounds (3.6) are stated in the equivalent $\varepsilon$-form: for every $\varepsilon>0$, eventually as $t\uparrow\tau$, $\varphi_-(p,e)-\varepsilon\le v(t,p_t,e_t)\le\varphi_+(p,e)+\varepsilon$.
-- source:
--   Chassagneux, Chotai & Crisan, Modelling multi-period carbon markets using singular forward-backward SDEs, arXiv:2008.09044v1, p. 14, Proposition 3.2, (3.4)–(3.6)

import Mathlib
import Definitions.Def_CarbonFBSDE_MultiPeriod_Model

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped NNReal ENNReal Topology

namespace CarbonFBSDE.MultiPeriod

universe u

theorem proposition_3_2 (d : ℕ) (r L : ℝ) (τ : ℝ≥0) (Lφ : ℝ) :
    ∃ C : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (B : Basis d Ω), B.Valid →
    ∀ (c : Coeffs d) (l1 l2 : ℝ), Assumption1 c L l1 l2 →
    ∀ φ : SDEState d → ℝ → ℝ, InK φ Lφ → 0 < τ →
    (∀ t0 < τ, ∀ (p : SDEState d) (e : ℝ),
      (∃ P E Y Z, IsOnePeriodSol B c r φ t0 τ p e P E Y Z) ∧
      (∀ P E Y Z P' E' Y' Z', IsOnePeriodSol B c r φ t0 τ p e P E Y Z →
        IsOnePeriodSol B c r φ t0 τ p e P' E' Y' Z' →
        SolAgree B (Icc t0 τ) (Ico t0 τ) t0 τ P E Y Z P' E' Y' Z')) ∧
    ∃ v : ℝ≥0 → SDEState d → ℝ → ℝ, IsValueFn₀ B c r φ τ v ∧
      ContinuousOn (fun x : ℝ≥0 × SDEState d × ℝ => v x.1 x.2.1 x.2.2) (Ico 0 τ ×ˢ univ) ∧
      (∀ t < τ, ∀ (p : SDEState d) (e e' : ℝ),
        |v t p e - v t p e'| ≤ 1 / (l1 * ((τ : ℝ) - t)) * |e - e'|) ∧
      (∀ t < τ, ∀ (p p' : SDEState d) (e : ℝ), |v t p e - v t p' e| ≤ C * ‖p - p'‖) ∧
      (∀ (p : SDEState d) (e : ℝ) (pt : ℝ≥0 → SDEState d) (et : ℝ≥0 → ℝ),
        Tendsto (fun t => (pt t, et t)) (𝓝[<] τ) (𝓝 (p, e)) → ∀ ε > 0,
          ∀ᶠ t in 𝓝[<] τ, lowerVer φ p e - ε ≤ v t (pt t) (et t) ∧
            v t (pt t) (et t) ≤ upperVer φ p e + ε) := by sorry

end CarbonFBSDE.MultiPeriod
