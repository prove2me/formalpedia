-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_seq_a
-- name    : Formalism.CyclotomicNorms.CentralScalarSequence.seq_a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:43.296567+00:00
-- url     : https://prove2.me/theorems/09a3332b-9a17-4177-b2da-15cf19a75263
-- title:
--   Central Scalar Sequence: seq a
-- statement:
--   The Central Scalar Sequence construction uses the seq a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L47-L50

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

theorem Formalism.CyclotomicNorms.CentralScalarSequence.seq_a (M j : ℕ) (h : j < M) : contrN j (insN (M + 1) a y) = insN M a (contrN j y) := by sorry
