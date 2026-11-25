-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_mem_Forms
-- name    : Formalism.L2.DIV.CSD.mem_Forms
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:43:43.160891+00:00
-- url     : https://prove2.me/theorems/ec736453-b046-4d1b-b1ab-dfb8cff54d7d
-- title:
--   CSD: mem Forms
-- statement:
--   The CSD construction uses the mem Forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L14-L14

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

theorem Formalism.L2.DIV.CSD.mem_Forms (f : S.Cl → S.V) : f ∈ S.Forms ↔ ∀ c (γ : S.Gam c), S.ρ c γ (f c) = f c := by sorry
