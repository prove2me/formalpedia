-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_basis_rat
-- name    : Formalism.L2.DIV.CSD.basis_rat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:10.414968+00:00
-- url     : https://prove2.me/theorems/f90d2e33-4398-45ab-b83b-92dbf56883b4
-- title:
--   CSD: basis rat
-- statement:
--   The CSD construction uses the basis rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L71-L73

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem Formalism.L2.DIV.CSD.basis_rat (h : S.HasRatBasis) (i : Fin S.dim) : S.IsRat (S.basis i : S.Cl → S.V) := by sorry
