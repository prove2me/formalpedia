-- Prove2me | Theorems.Thm_CrossLayerControl_ECCA_drift_bound
-- name    : CrossLayerControl.ECCA.drift_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:38:26.190017+00:00
-- url     : https://prove2.me/theorems/08f6155b-bf89-4f27-b43b-866caf50e90b
-- title:
--   Eq. (6.11) for the downlink: per-slot drift-plus-penalty bound with explicit $B$
-- statement:
--   Assume the signs and the rate bound (3.4). Let $U\in\mathbb R^L$ and $D\in\mathbb R$ be nonnegative backlogs, $s$ a state, $R$ admitted data with $0\le R_i\le\hat R$, and $P$ a feasible power vector, and let
--   $$U'_i=\max[U_i-C_i(P,s),0]+R_i,\qquad D'=\max[D-P_{av},0]+\sum_iP_i$$
--   be the next-slot backlogs. Then for every real $V$,
--   $$\tfrac12\Big(\sum_iU_i'^2+D'^2\Big)-\tfrac12\Big(\sum_iU_i^2+D^2\Big)-V\sum_iR_i\le B+\sum_i(U_i-V)R_i-\sum_i\big[U_iC_i(P,s)-DP_i\big]-DP_{av},$$
--   with $B=\tfrac12\big(L(\mu_{max}^2+\hat R^2)+P_{av}^2+P_{max}^2\big)$.
--
--   This is the bound (6.11) specialized to the downlink ($f=0$, $g(R)=\sum_iR_i$, $q(P)=\sum_iP_i$, $Q=P_{av}$, no auxiliary queues), with the Lyapunov function $\tfrac12(\sum_iU_i^2+D^2)$. ECCA minimizes its right-hand side.
--
--   Differences from the source:
--   - generalization: (6.11): a bound on the conditional drift given the queue state, with V > 0 → the inequality for every realization of one slot, for every real V; reason: taking conditional expectations of the per-slot inequality gives (6.11)
--   - reading: B a finite positive constant, unspecified → B = (L(µmax² + R̂²) + Pav² + Pmax²)/2; reason: the constant obtained from Lemma 4.3 for the L data queues and the virtual power queue; it does not depend on V
--   - reading: signs of Pav, Pmax, R̂ unstated → 0 ≤ Pav, 0 ≤ Pmax, 0 ≤ R̂ (RateHyp); reason: a negative average power budget is unsatisfiable; R̂ ≥ 0 is forced by 0 ≤ A_i ≤ R̂ when L ≥ 1 and keeps L = 0 nondegenerate; Pmax ≥ 0 follows from 0 ≤ Pav < Pmax
--   - encoding: power vectors with Σ P_i ≤ Pmax → power vectors with P_i ≥ 0 and Σ P_i ≤ Pmax; reason: power is nonnegative; the page leaves it implicit
--   - generalization: 0 ≤ R_i(t) ≤ A_i(t) ≤ R̂ → 0 ≤ R_i ≤ R̂ (no arrival vector); reason: a weaker hypothesis; every flow decision of the source satisfies it
--   - encoding: links 1,…,L → Fin L (0-based); reason: Lean convention; same instances
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, (6.11), p. 109, specialized on p. 114 (¶1) and p. 113 (f, g, q, Q)

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_IsFeasiblePower
import Definitions.Def_CrossLayerControl_ECCA_RateHyp
import Definitions.Def_CrossLayerControl_ECCA_B

namespace CrossLayerControl.ECCA

/-- **The drift-plus-penalty bound (6.11) for the downlink, in per-slot form.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), (6.11), p. 109: "∆(Θ(t)) + V E{f(α(t)) − g(γ(t))|Θ(t)} ≤ B −
Σ_{n,c} U(c)n(t)E{Σ_b µ(c)nb(t) − Σ_a µ(c)an(t) − R(c)n(t) | Θ(t)} − Σ_{i=1}^{Jq} Di,q(t)[Qi −
E{qi(α(t))|Θ(t)}] − … + V E{f(α(t)) − g(γ(t))|Θ(t)}, (6.11) where B is a finite and positive
constant." Specialized on p. 114: "we can avoid the virtual queues Zx(t) and simply use
α(t) = x(t) = P(t) everywhere … and simply use γ(t) = y(t) = R(t)", with f = 0, g(R) = Σᵢ Rᵢ,
q(P) = Σᵢ Pᵢ, Q = Pav (p. 113).

Assume `RateHyp M`. Let `U ∈ ℝ^L` and `D ∈ ℝ` be nonnegative backlogs, `s` a state, `R` admitted data
with `0 ≤ Rᵢ ≤ R̂`, and `P` a feasible power vector. Let `U'ᵢ = max (Uᵢ − Cᵢ(P, s)) 0 + Rᵢ` and
`D' = max (D − Pav) 0 + Σᵢ Pᵢ` be the next-slot backlogs. Then, for every real `V`, with the
Lyapunov function `(Σᵢ Uᵢ² + D²)/2`,
`(Σᵢ U'ᵢ² + D'²)/2 − (Σᵢ Uᵢ² + D²)/2 − V Σᵢ Rᵢ
   ≤ B + Σᵢ (Uᵢ − V) Rᵢ − Σᵢ (Uᵢ Cᵢ(P, s) − D Pᵢ) − D Pav`,
with `B = (L(µmax² + R̂²) + Pav² + Pmax²)/2` (`B M`).

**Formalization Note.** The paper states (6.11) for conditional expectations given the queue state
and leaves B unspecified. This per-slot inequality implies the conditional form by taking
conditional expectations, and fixes B explicitly, independently of `V`. The right-hand side is the
paper's: `−Σᵢ Uᵢ E{Cᵢ − Rᵢ} − D (Pav − Σᵢ Pᵢ) − V Σᵢ Rᵢ`, regrouped. -/
theorem drift_bound {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (hM : RateHyp M) (V : ℝ)
    (U : Fin L → ℝ) (D : ℝ) (hU : ∀ i, 0 ≤ U i) (hD : 0 ≤ D)
    (s : 𝒮) (R P : Fin L → ℝ) (hR : ∀ i, 0 ≤ R i ∧ R i ≤ M.Rhat) (hP : IsFeasiblePower M P) :
    (∑ i, (max (U i - M.C i P s) 0 + R i) ^ 2 + (max (D - M.Pav) 0 + ∑ i, P i) ^ 2) / 2 -
        (∑ i, U i ^ 2 + D ^ 2) / 2 - V * ∑ i, R i ≤
      B M + ∑ i, (U i - V) * R i - ∑ i, (U i * M.C i P s - D * P i) - D * M.Pav := by sorry

end CrossLayerControl.ECCA
