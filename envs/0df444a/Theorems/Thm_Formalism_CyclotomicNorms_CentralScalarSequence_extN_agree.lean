-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_extN_agree
-- name    : Formalism.CyclotomicNorms.CentralScalarSequence.extN_agree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:35.606671+00:00
-- url     : https://prove2.me/theorems/bd74771d-0df0-40ce-b298-2d28e04dfd2a
-- title:
--   Central Scalar Sequence: ext N agree
-- statement:
--   The Central Scalar Sequence construction uses the ext N agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L21-L22

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.CentralScalarSequence
variable {G : Type} [Group G]

theorem Formalism.CyclotomicNorms.CentralScalarSequence.extN_agree {m : ℕ} (x : Fin m → G) : ∀ k : Fin m, x k = extN x k := by sorry
