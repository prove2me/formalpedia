-- Prove2me | Theorems.Thm_CrossLayerControl_ECCA_ecca_drift_comparison
-- name    : CrossLayerControl.ECCA.ecca_drift_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:38:59.268883+00:00
-- url     : https://prove2.me/theorems/db7bf2e4-4eac-43eb-a888-3e95a69ce03f
-- title:
--   ECCA minimizes the right-hand side of (6.11): comparison with stationary randomized decisions
-- statement:
--   Assume the signs, the rate bound (3.4) and measurable rates, nonnegative initial backlogs, and a probability space with a filtration $(\mathcal F_t)$ on which the arrivals $0\le A_i(t)\le\hat R$ and states $S(t)$ are i.i.d. over slots with slot law $\mu$ relative to $(\mathcal F_t)$. Let the decisions $R(t)$, $P(t)$ be $\mathcal F_t$-measurable and form an ECCA run on every sample path, and write $\Lambda(t)=\tfrac12\big(\sum_iU_i(t)^2+D(t)^2\big)$. Then for every triple $(r,c,p)$ of rate, service and power expectations of a stationary randomized decision (an element of $K(\mu)$) and every slot $t$,
--   $$\mathbb E\{\Lambda(t+1)\}-\mathbb E\{\Lambda(t)\}-V\sum_i\mathbb E\{R_i(t)\}\le B-V\sum_ir_i+\sum_i\mathbb E\{U_i(t)\}(r_i-c_i)+\mathbb E\{D(t)\}(p-P_{av}).$$
--
--   ECCA's decisions minimize the right-hand side of the drift bound (6.11) every slot, so its expected drift-plus-penalty is at most that of any stationary randomized decision. Summed over slots with Lemma 5.3, this gives the throughput clause of Theorem 6.3.
--
--   Differences from the source:
--   - reading: minimizing the right hand side of (6.11) leads to ECCA (design principle) → the expected drift-plus-penalty of ECCA is at most B − V Σ r_i + Σ E U_i (r_i − c_i) + E D (p − Pav) for every stationary randomized decision; reason: the comparison is how [116] uses the principle and what the throughput clause needs
--   - reading: B unspecified → B = (L(µmax² + R̂²) + Pav² + Pmax²)/2; reason: the constant of the drift bound (6.11) for the downlink; independent of V
--   - reading: the pair [S(t); A(t)] i.i.d. over timeslots → (A(t), S(t)) has law µ, is F_t-measurable and (A(t+1), S(t+1)) is independent of F_t, with decisions F_t-adapted; reason: the i.i.d. assumption relative to the controller's information; for the natural filtration it is the paper's
--   - generalization: ECCA with the rule admit everything iff U_i(t) ≤ V and a maximizer of (6.14) → any minimizer of the flow-control objective and any maximizer of (6.14) (IsECCARun); reason: ties broken arbitrarily; the paper's run is one of these
--   - generalization: S-only algorithms (decisions depending on S(t)) → stationary randomized decisions depending on (A(t), S(t)), V any real; reason: flow control needs the current arrivals; S-only decisions are a special case
--   - reading: signs of Pav, Pmax, R̂ unstated → 0 ≤ Pav, 0 ≤ Pmax, 0 ≤ R̂ (RateHyp); reason: a negative average power budget is unsatisfiable; R̂ ≥ 0 is forced by 0 ≤ A_i ≤ R̂ when L ≥ 1 and keeps L = 0 nondegenerate; Pmax ≥ 0 follows from 0 ≤ Pav < Pmax
--   - encoding: expectations of the rates → measurable rate function (DownlinkMeas); reason: Lean integrals of non-measurable functions are 0
--   - encoding: power vectors with Σ P_i ≤ Pmax → power vectors with P_i ≥ 0 and Σ P_i ≤ Pmax; reason: power is nonnegative; the page leaves it implicit
--   - encoding: A_i(t) ≤ R̂ → 0 ≤ A_i(t) ≤ R̂; reason: arrivals are amounts of data, hence nonnegative; with A_i(t) < 0 the flow-control constraint 0 ≤ R_i(t) ≤ A_i(t) is infeasible and no ECCA run (or admissible decision) exists, so no instance is excluded
--   - encoding: links 1,…,L → Fin L (0-based); reason: Lean convention; same instances
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, p. 114 (sentence before ECCA); p. 109 (last sentence); Definition 6.1, p. 103

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_RateHyp
import Definitions.Def_CrossLayerControl_ECCA_DownlinkMeas
import Definitions.Def_CrossLayerControl_ECCA_queueU
import Definitions.Def_CrossLayerControl_ECCA_virtD
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun
import Definitions.Def_CrossLayerControl_ECCA_IsAdaptedIID
import Definitions.Def_CrossLayerControl_ECCA_achievable
import Definitions.Def_CrossLayerControl_ECCA_B

open MeasureTheory

namespace CrossLayerControl.ECCA

/-- **ECCA minimizes the right-hand side of (6.11): the expected drift-plus-penalty of ECCA is at
most that of any stationary randomized decision.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), p. 114 (unnumbered): "With these simplifications, minimizing the
right hand side of (6.11) leads to the following Energy Constrained Control Algorithm (ECCA) from
[116]:"; p. 109: "Every timeslot, the control decision variables are chosen to minimize the right
hand side of the above inequality."; Definition 6.1, p. 103: "An S-only algorithm is a stationary
randomized algorithm that chooses control variables … based only on the current topology state
S(t)."

Assume `RateHyp M` and `DownlinkMeas M`, nonnegative initial backlogs `u₀`, a probability space
`(Ω, Pr)` with filtration `ℱ`, arrivals `0 ≤ Aᵢ(t) ≤ R̂` and states `S(t)` whose pair is i.i.d. with
law `μ` relative to `ℱ` (`IsAdaptedIID`), and decisions `R(t)`, `P(t)` that are `ℱ t`-measurable and
form an ECCA run on every sample path. Write `Uᵢ(t)`, `D(t)` for the backlogs and
`Λ(t) = (Σᵢ Uᵢ(t)² + D(t)²)/2`. Then for every triple `(r, c, p)` of `achievable M μ` (the
expectations `E R`, `E C(P, S)`, `E Σ P` of a stationary randomized decision) and every slot `t`,
`E Λ(t+1) − E Λ(t) − V Σᵢ E Rᵢ(t)
   ≤ B − V Σᵢ rᵢ + Σᵢ E[Uᵢ(t)] (rᵢ − cᵢ) + E[D(t)] (p − Pav)`.

**Formalization Note.** The paper states the design principle in this sentence; the comparison is
the form in which [116] uses it, and the one Theorem 6.3's throughput clause needs. `B` is the
explicit constant `B M`. ECCA is a relation (any tie-breaking), and `V` is any real. -/
theorem ecca_drift_comparison {L : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮] (M : Downlink L 𝒮)
    (hM : RateHyp M) (hMm : DownlinkMeas M) (V : ℝ) (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (ℱ : Filtration ℕ mΩ) (A : ℕ → Ω → Fin L → ℝ) (S : ℕ → Ω → 𝒮) (R P : ℕ → Ω → Fin L → ℝ)
    (μ : Measure ((Fin L → ℝ) × 𝒮)) (hiid : IsAdaptedIID Pr ℱ A S μ)
    (hA : ∀ t ω i, 0 ≤ A t ω i ∧ A t ω i ≤ M.Rhat)
    (hRP : ∀ t, Measurable[ℱ t] (R t) ∧ Measurable[ℱ t] (P t))
    (hrun : ∀ ω, IsECCARun M V u₀ (fun t => A t ω) (fun t => S t ω) (fun t => R t ω)
      (fun t => P t ω))
    (q : (Fin L → ℝ) × (Fin L → ℝ) × ℝ) (hq : q ∈ achievable M μ) (t : ℕ) :
    (∫ ω, (∑ i, queueU M u₀ (fun τ => S τ ω) (fun τ => R τ ω) (fun τ => P τ ω) (t + 1) i ^ 2 +
          virtD M (fun τ => P τ ω) (t + 1) ^ 2) / 2 ∂Pr) -
        (∫ ω, (∑ i, queueU M u₀ (fun τ => S τ ω) (fun τ => R τ ω) (fun τ => P τ ω) t i ^ 2 +
          virtD M (fun τ => P τ ω) t ^ 2) / 2 ∂Pr) -
        V * ∑ i, ∫ ω, R t ω i ∂Pr ≤
      B M - V * ∑ i, q.1 i +
        ∑ i, (∫ ω, queueU M u₀ (fun τ => S τ ω) (fun τ => R τ ω) (fun τ => P τ ω) t i ∂Pr) *
          (q.1 i - q.2.1 i) +
        (∫ ω, virtD M (fun τ => P τ ω) t ∂Pr) * (q.2.2 - M.Pav) := by sorry

end CrossLayerControl.ECCA
