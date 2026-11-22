-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_I_onto
-- name    : Formalism.L2.DIV.CSD.I_onto
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:18.139904+00:00
-- url     : https://prove2.me/theorems/80085590-576a-4a22-a7cc-c68af6361833
-- title:
--   CSD: I onto
-- statement:
--   The CSD construction uses the I onto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L23-L28

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

theorem Formalism.L2.DIV.CSD.I_onto (f : S.Cl → S.V) : (∃ x, S.I x = f) ↔ ∀ c (γ : S.Gam c), S.ρ c γ (f c) = f c := by sorry
