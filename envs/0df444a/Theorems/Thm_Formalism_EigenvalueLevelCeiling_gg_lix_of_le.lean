-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_gg_lix_of_le
-- name    : Formalism.EigenvalueLevelCeiling.gg_lix_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:24.450335+00:00
-- url     : https://prove2.me/theorems/b56f8de9-a2ea-44db-99cb-30ca7bbde503
-- title:
--   Eigenvalue Level Ceiling: gg lix of le
-- statement:
--   The Eigenvalue Level Ceiling construction uses the gg lix of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L183-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L183-L187

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

theorem Formalism.EigenvalueLevelCeiling.gg_lix_of_le (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) Z) (h : B ≤ A) :
    lix w A B = (Formalism.HermitianLatticesTheory.locLen w.asIdeal A B : ℤ) := by sorry
