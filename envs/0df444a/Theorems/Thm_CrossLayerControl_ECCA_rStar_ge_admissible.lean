-- Prove2me | Theorems.Thm_CrossLayerControl_ECCA_rStar_ge_admissible
-- name    : CrossLayerControl.ECCA.rStar_ge_admissible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:40:46.405264+00:00
-- url     : https://prove2.me/theorems/798ae567-ca2c-4800-94be-ffdd07a3493b
-- title:
--   Theorem 6.3: $\sum_i r_i^*$ is the optimal throughput over all possible policies (converse)
-- statement:
--   Assume the signs, the rate bound (3.4) and measurable rates. On a probability space, let the arrivals satisfy $0\le A_i(t)\le\hat R$ and let $(A(t),S(t))$ be measurable with law $\mu$ at every slot. Then every admissible policy $(R,P)$ — pointwise feasible, measurable, with mean-rate stable queues from any initial backlog, and average power at most $P_{av}$ — satisfies
--   $$\limsup_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\sum_{i=1}^L\mathbb E\{R_i(\tau)\}\le\sum_ir_i^*.$$
--
--   No policy, causal or not, exceeds the benchmark $\sum_i r_i^*$; together with the throughput clause of Theorem 6.3 this identifies $\sum_ir_i^*$ as the optimal throughput.
--
--   Differences from the source:
--   - reading: Σ_i r*_i, the optimal throughput over all possible policies → rStar: the supremum of Σ_i r_i over the closure of the stationary randomized triples with r ≤ c and p ≤ Pav; reason: the paper gives no formula; this statement shows that rStar bounds every admissible policy
--   - generalization: all possible policies → all admissible policies: measurable, mean-rate stable, average power ≤ Pav, not necessarily causal, without any independence of (A, S) across slots; reason: the class contains the paper's strongly stable policies (Lemma 3.3)
--   - reading: signs of Pav, Pmax, R̂ unstated → 0 ≤ Pav, 0 ≤ Pmax, 0 ≤ R̂ (RateHyp); reason: a negative average power budget is unsatisfiable; R̂ ≥ 0 is forced by 0 ≤ A_i ≤ R̂ when L ≥ 1 and keeps L = 0 nondegenerate; Pmax ≥ 0 follows from 0 ≤ Pav < Pmax
--   - encoding: expectations of rates; limsup → measurable rate function; limsup in EReal; reason: Lean conventions for integrals and limits
--   - encoding: power vectors with Σ P_i ≤ Pmax → power vectors with P_i ≥ 0 and Σ P_i ≤ Pmax; reason: power is nonnegative; the page leaves it implicit
--   - encoding: A_i(t) ≤ R̂ → 0 ≤ A_i(t) ≤ R̂; reason: arrivals are amounts of data, hence nonnegative; with A_i(t) < 0 the flow-control constraint 0 ≤ R_i(t) ≤ A_i(t) is infeasible and no ECCA run (or admissible decision) exists, so no instance is excluded
--   - encoding: links 1,…,L → Fin L (0-based); reason: Lean convention; same instances
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Theorem 6.3, p. 115 (last sentence); p. 105

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_RateHyp
import Definitions.Def_CrossLayerControl_ECCA_DownlinkMeas
import Definitions.Def_CrossLayerControl_ECCA_throughputAvg
import Definitions.Def_CrossLayerControl_ECCA_IsAdmissiblePolicy
import Definitions.Def_CrossLayerControl_ECCA_rStar

open MeasureTheory Filter

namespace CrossLayerControl.ECCA

/-- **Σᵢ r∗ᵢ is the optimal throughput over all possible policies (the converse).**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Theorem 6.3, p. 115 (unnumbered): "where Σi r∗i is the optimal
throughput over all possible policies, and B is a constant that can be computed from the Lyapunov
drift of the system [116]."; p. 105: "For a large class of network flow problems, including … the
energy problems to be presented in this section, c∗ is also the optimal cost over all possible
(perhaps not S-only) policies [116]."

Assume `RateHyp M` and `DownlinkMeas M`. On a probability space `(Ω, Pr)`, let the arrivals satisfy
`0 ≤ Aᵢ(t) ≤ R̂`, and let the pair `(A(t), S(t))` be measurable with law `μ` at every slot. Then
every admissible policy `(R, P)` (`IsAdmissiblePolicy`: pointwise constraints, measurable,
mean-rate stable queues from any initial backlog `u₀`, average power at most `Pav`) satisfies
`limsup_{t→∞} (1/t) Σ_{τ<t} Σᵢ E Rᵢ(τ) ≤ Σᵢ r∗ᵢ` (`rStar M μ`).

**Formalization Note.** No independence and no causality is assumed: the bound holds for every
policy, anticipating or not, as long as the slot law of `(A(t), S(t))` is `μ`. The `limsup` is taken
in `EReal`, so it is never a junk value. -/
theorem rStar_ge_admissible {L : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮] (M : Downlink L 𝒮)
    (hM : RateHyp M) (hMm : DownlinkMeas M)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (A : ℕ → Ω → Fin L → ℝ) (S : ℕ → Ω → 𝒮) (R P : ℕ → Ω → Fin L → ℝ) (u₀ : Fin L → ℝ)
    (μ : Measure ((Fin L → ℝ) × 𝒮))
    (hAS : ∀ t, Measurable (fun ω => (A t ω, S t ω)))
    (hlaw : ∀ t, Pr.map (fun ω => (A t ω, S t ω)) = μ)
    (hA : ∀ t ω i, 0 ≤ A t ω i ∧ A t ω i ≤ M.Rhat)
    (hadm : IsAdmissiblePolicy M Pr A S R P u₀) :
    limsup (fun t : ℕ => (throughputAvg Pr R t : EReal)) atTop ≤ (rStar M μ : EReal) := by sorry

end CrossLayerControl.ECCA
