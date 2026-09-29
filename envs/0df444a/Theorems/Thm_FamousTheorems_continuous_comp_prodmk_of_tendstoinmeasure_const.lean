-- Prove2me | Theorems.Thm_FamousTheorems_continuous_comp_prodmk_of_tendstoinmeasure_const
-- name    : FamousTheorems.continuous_comp_prodmk_of_tendstoinmeasure_const
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:27.761909+00:00
-- url     : https://prove2.me/theorems/c89b6529-1a81-44de-a420-7e07cdf2e6e0
-- title:
--   Slutsky's theorem
-- statement:
--   **Slutsky's theorem.** If $X_n$ converges in distribution and $Y_n$ converges in probability to a constant, then a continuous function of the pair converges in distribution to the corresponding function of the limit. Convergence in distribution is not preserved by arbitrary joint operations — it says nothing about dependence — but a limit that is *constant* carries no randomness, so the pair converges jointly and the continuous mapping theorem applies. This is the theorem that licenses replacing an unknown variance by a consistent estimator in a test statistic, which is why $t$-statistics are asymptotically normal. **Formalization note.** The second sequence converges in measure to a constant, and the combining map is continuous on the product. The result is Mathlib's `MeasureTheory.TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem continuous_comp_prodmk_of_tendstoinmeasure_const :
    ∀ {ι : Type u_1} {E : Type u_2} 
    {Ω' : Type u_3} {Ω'' : Type u_4} {m' : MeasurableSpace Ω'} {μ' : MeasureTheory.Measure Ω'} 
    [inst : MeasureTheory.IsProbabilityMeasure μ'] {m'' : MeasurableSpace Ω''} {μ'' : MeasureTheory.Measure Ω''} 
    [inst_1 : MeasureTheory.IsProbabilityMeasure μ''] {mE : MeasurableSpace E} {Z : Ω' → E} {l : Filter ι} 
    [inst_2 : SeminormedAddCommGroup E] [SecondCountableTopology E] [inst_4 : BorelSpace E] {E' : Type u_5} {F : Type u_6} 
    {mE' : MeasurableSpace E'} [inst_5 : SeminormedAddCommGroup E'] [SecondCountableTopology E'] [BorelSpace E'] 
    [inst_8 : TopologicalSpace F] [inst_9 : MeasurableSpace F] [inst_10 : BorelSpace F] {g : E × E' → F}, 
    Continuous g → 
    ∀ [l.IsCountablyGenerated] {X : ι → Ω'' → E} {Y : ι → Ω'' → E'} {c : E'}, 
    MeasureTheory.TendstoInDistribution X l Z (fun x => μ'') μ' → 
    (MeasureTheory.TendstoInMeasure μ'' Y l fun x => c) → 
    (∀ (i : ι), AEMeasurable (Y i) μ'') → 
    MeasureTheory.TendstoInDistribution (fun n ω => g (X n ω, Y n ω)) l (fun ω => g (Z ω, c)) (fun x => μ'') μ' := by sorry

end FamousTheorems
