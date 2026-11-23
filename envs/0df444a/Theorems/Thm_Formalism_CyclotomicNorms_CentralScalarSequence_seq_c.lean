-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_seq_c
-- name    : Formalism.CyclotomicNorms.CentralScalarSequence.seq_c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:52.13607+00:00
-- url     : https://prove2.me/theorems/e548a52b-f1b2-46df-82a6-c3bcd697196d
-- title:
--   Central Scalar Sequence: seq c
-- statement:
--   The Central Scalar Sequence construction uses the seq c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L58-L61

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
variable (a : G) (y : ℕ → G)

theorem Formalism.CyclotomicNorms.CentralScalarSequence.seq_c (M i : ℕ) (h : i ≤ M) : contrN (M + 1) (insN i a y) = insN i a (contrN M y) := by sorry
