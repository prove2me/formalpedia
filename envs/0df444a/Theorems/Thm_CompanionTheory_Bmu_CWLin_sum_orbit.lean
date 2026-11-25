-- Prove2me | Theorems.Thm_CompanionTheory_Bmu_CWLin_sum_orbit
-- name    : CompanionTheory.Bmu.CWLin.sum_orbit
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:14:11.773128+00:00
-- url     : https://prove2.me/theorems/d934106d-07f2-5b07-a984-e4d6b3b1e76a
-- title:
--   CWLin: sum orbit
-- statement:
--   The CWLin construction uses the sum orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ContinuousOnOrbit.lean#L65-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ContinuousOnOrbit.lean#L65-L74

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {Hm : Mat n} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat n → (H →L[ℂ] H)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
omit [CompleteSpace H]

theorem CompanionTheory.Bmu.CWLin.sum_orbit (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {w : H} (hw : IsSm (UH Hm) σ w)
    (h0 : ∀ g ∈ UH Hm, B (σ g w) = 0) {ι : Type} (s : Finset ι) (c : ι → ℂ) (g : ι → Mat n)
    (hg : ∀ i, g i ∈ UH Hm) : IsSm (UH Hm) σ (∑ i ∈ s, c i • σ (g i) w) ∧ B (∑ i ∈ s, c i • σ (g i) w) = 0 := by sorry
