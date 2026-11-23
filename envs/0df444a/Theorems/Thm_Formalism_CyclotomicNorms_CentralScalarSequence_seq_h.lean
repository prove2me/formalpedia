-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_seq_h
-- name    : Formalism.CyclotomicNorms.CentralScalarSequence.seq_h
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:43.398025+00:00
-- url     : https://prove2.me/theorems/d9e9ab88-8883-4cff-900f-18680477708c
-- title:
--   Central Scalar Sequence: seq h
-- statement:
--   The Central Scalar Sequence construction uses the seq h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L75-L76

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

theorem Formalism.CyclotomicNorms.CentralScalarSequence.seq_h (n k : ℕ) (hk : k < n + 1) : contrN (n + 1) (insN (n + 1) a y) k = y k := by sorry
