-- Prove2me | Theorems.Thm_Formalism_L2_NT_offs_add_le_sum
-- name    : Formalism.L2.NT.offs_add_le_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:55:58.914946+00:00
-- url     : https://prove2.me/theorems/3e032331-3466-4a27-9bca-e71c583470e1
-- title:
--   NT: offs add le sum
-- statement:
--   The NT construction uses the offs add le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L288-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L288-L298

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem Formalism.L2.NT.offs_add_le_sum {m : ℕ} (c : Fin m → ℕ) (i : Fin m) : offs c i + c i ≤ ∑ k, c k := by sorry
