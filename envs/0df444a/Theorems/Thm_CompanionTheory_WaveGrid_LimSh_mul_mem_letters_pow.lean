-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_LimSh_mul_mem_letters_pow
-- name    : CompanionTheory.WaveGrid.LimSh.mul_mem_letters_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:14.595993+00:00
-- url     : https://prove2.me/theorems/678dde91-832c-4234-9c5c-b579c18c09d8
-- title:
--   Lim Sh: mul mem letters pow
-- statement:
--   The Lim Sh construction uses the mul mem letters pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/LettersPoly.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/LettersPoly.lean#L27-L30

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_LettersPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.WaveGrid CompanionTheory.WaveGrid.LimSh
open Formalism.FourierDecayAlt Matrix CompanionTheory.LimBd.Main
variable {k r : ℕ}

theorem CompanionTheory.WaveGrid.LimSh.mul_mem_letters_pow {a d : ℕ} {x y : B.Mat k r → ℂ} (hx : x ∈ Letters k r ^ a) (hy : y ∈ Letters k r ^ d) :
    x * y ∈ Letters k r ^ (a + d) := by sorry
