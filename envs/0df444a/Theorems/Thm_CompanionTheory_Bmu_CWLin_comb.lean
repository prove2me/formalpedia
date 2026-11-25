-- Prove2me | Theorems.Thm_CompanionTheory_Bmu_CWLin_comb
-- name    : CompanionTheory.Bmu.CWLin.comb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:17:42.372803+00:00
-- url     : https://prove2.me/theorems/1f2c2484-b675-440c-9f01-419704e3c972
-- title:
--   CWLin: comb
-- statement:
--   The CWLin construction uses the comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ContinuousOnOrbit.lean#L34-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ContinuousOnOrbit.lean#L34-L58

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

theorem CompanionTheory.Bmu.CWLin.comb {B₁ B₂ : H → V} (h₁ : CWLin Hm σ B₁) (h₂ : CWLin Hm σ B₂) (a b : ℂ) :
    CWLin Hm σ (fun v => a • B₁ v + b • B₂ v) := by sorry
