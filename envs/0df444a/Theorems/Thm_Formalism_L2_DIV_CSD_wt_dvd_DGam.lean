-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_wt_dvd_DGam
-- name    : Formalism.L2.DIV.CSD.wt_dvd_DGam
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:10.522595+00:00
-- url     : https://prove2.me/theorems/a8de40da-7e1a-4d78-800d-c324537c7741
-- title:
--   CSD: wt dvd DGam
-- statement:
--   The CSD construction uses the wt dvd DGam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L58-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L58-L58

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

theorem Formalism.L2.DIV.CSD.wt_dvd_DGam (c : S.Cl) : S.wt c ∣ S.DGam := by sorry
