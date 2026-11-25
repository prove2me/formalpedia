-- Prove2me | Theorems.Thm_CompanionTheory_Bmu_CWLin_comp_sigma
-- name    : CompanionTheory.Bmu.CWLin.comp_sigma
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:16:57.077335+00:00
-- url     : https://prove2.me/theorems/7a36d7f2-5e83-5560-b901-4164e184e5c3
-- title:
--   CWLin: comp sigma
-- statement:
--   The CWLin construction uses the comp sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ContinuousOnOrbit.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ContinuousOnOrbit.lean#L17-L31

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

theorem CompanionTheory.Bmu.CWLin.comp_sigma (hAd : DsAd) (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {y : Mat n}
    (hy : y ∈ UH Hm) : CWLin Hm σ (fun v => B (σ y v)) := by sorry
