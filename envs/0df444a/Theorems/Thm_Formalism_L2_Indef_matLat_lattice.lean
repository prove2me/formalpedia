-- Prove2me | Theorems.Thm_Formalism_L2_Indef_matLat_lattice
-- name    : Formalism.L2.Indef.matLat_lattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:16.187904+00:00
-- url     : https://prove2.me/theorems/cf510ace-5439-4410-bf4e-0c67692eee93
-- title:
--   Indef: mat Lat lattice
-- statement:
--   The Indef construction uses the mat Lat lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L207-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L207-L215

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.Indef.matLat_lattice {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) K) (h : Function.Surjective φ.mulVec)
    (L : Submodule (𝓞 K) (Fin d → K)) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (matLat φ L) := by sorry
