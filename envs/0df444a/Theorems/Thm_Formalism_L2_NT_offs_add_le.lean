-- Prove2me | Theorems.Thm_Formalism_L2_NT_offs_add_le
-- name    : Formalism.L2.NT.offs_add_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:23.745878+00:00
-- url     : https://prove2.me/theorems/85d57d61-b5b7-4f18-ba26-df34100fbae2
-- title:
--   NT: offs add le
-- statement:
--   The NT construction uses the offs add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L273-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L273-L286

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

theorem Formalism.L2.NT.offs_add_le {m : ℕ} (c : Fin m → ℕ) {i j : Fin m} (h : j < i) : offs c j + c j ≤ offs c i := by sorry
