-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_mapsTo_locP
-- name    : Formalism.EigenvalueLevelCeiling.mapsTo_locP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:39.012972+00:00
-- url     : https://prove2.me/theorems/4072fe7f-4beb-4e0e-97e8-ad8b519ff65f
-- title:
--   Eigenvalue Level Ceiling: maps To loc P
-- statement:
--   The Eigenvalue Level Ceiling construction uses the maps To loc P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L177-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L177-L181

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

theorem Formalism.EigenvalueLevelCeiling.mapsTo_locP {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (f : W →ₗ[R] W) (X Y : Submodule R W) (h : ∀ x ∈ X, f x ∈ Y) :
    ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ p X, f x ∈ Formalism.HermitianLatticesTheory.localization₂ p Y := by sorry
