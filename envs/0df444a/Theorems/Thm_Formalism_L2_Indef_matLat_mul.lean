-- Prove2me | Theorems.Thm_Formalism_L2_Indef_matLat_mul
-- name    : Formalism.L2.Indef.matLat_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:24.357848+00:00
-- url     : https://prove2.me/theorems/31efe9db-3d10-47c2-a3f9-9d3d62feec93
-- title:
--   Indef: mat Lat mul
-- statement:
--   The Indef construction uses the mat Lat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L391-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L391-L402

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

theorem Formalism.L2.Indef.matLat_mul {d d' d'' : ℕ} (A : Matrix (Fin d'') (Fin d') K) (B : Matrix (Fin d') (Fin d) K)
    (L : Submodule (𝓞 K) (Fin d → K)) : matLat (A * B) L = matLat A (matLat B L) := by sorry
