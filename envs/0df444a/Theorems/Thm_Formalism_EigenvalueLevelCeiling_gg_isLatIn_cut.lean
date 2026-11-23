-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_gg_isLatIn_cut
-- name    : Formalism.EigenvalueLevelCeiling.gg_isLatIn_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:16.622191+00:00
-- url     : https://prove2.me/theorems/3ae0c6b1-89fd-47c3-aa70-991966e1c02e
-- title:
--   Eigenvalue Level Ceiling: gg is Lat In cut
-- statement:
--   The Eigenvalue Level Ceiling construction uses the gg is Lat In cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L189-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L189-L214

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

theorem Formalism.EigenvalueLevelCeiling.gg_isLatIn_cut [FiniteDimensional K Z] (W : Submodule K Z) (B : Submodule (𝓞 K) Z)
    (hB : IsLatIn ⊤ B) : IsLatIn W (cut W B) := by sorry
