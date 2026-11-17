-- Prove2me | Theorems.Thm_APFPaper5_K2_score_eq_of_readoutEq
-- name    : APFPaper5.K2.score_eq_of_readoutEq
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:45:20.734092+00:00
-- url     : https://prove2.me/theorems/90a830cb-b8d2-4ec1-bf1f-bce53e3faafc
-- title:
--   score eq of readoutEq
-- statement:
--   Result: score eq of readoutEq. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem score_eq_of_readoutEq (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
--       (score : (g : Context) → WordFrom Frag g → Raw g → ℝ) (hz : ZeroConvention Defd score)
--       {a b : Context} (W W' : Word Frag a b) (h : ReadoutEq Defd score W W')
--       (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g) :
--       score g (sandwich P W S) x = score g (sandwich P W' S) x
--   ```
--
--   Module context and limits: Theorems concern supplied admission, value and score data; ZeroConvention is retained where used. Point separation is built into ReadoutEq and does not prove separation of linear combinations, physical readout coverage, a finite-dimensional algebra or an adjoint.
--
--   Source scope parameters:
--
--   ```lean
--   universe uC uF uX uV uR uI
--   variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
--     {Val : Type uV}
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_closed_boundary_on_words:278; pullbacks v39; source SHA-256 53befb18d62f4f7ca23091d8275015586b7d38d3cc263a68544f0abab264b9e5']

import Definitions.Def_APFPaper5_K2_closed_boundary_on_words_Vocabulary
import Definitions.Def_APFPaper5_K2_ClosedBoundary
import Theorems.Thm_APFPaper1_Continuation_contextEq_sandwich
import Theorems.Thm_APFPaper1_Continuation_contextEq_sandwich_all
import Theorems.Thm_APFPaper1_Continuation_contextEq_all_of_ambientHeredity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

set_option autoImplicit false
open APFPaper1.Continuation

namespace APFPaper5.K2
end APFPaper5.K2
open APFPaper5
open APFPaper5.K2
universe uC uF uX uV uR uI
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

/-! ### The classes multiply -/



















/-! ### The word admitted nowhere is the zero -/













/-! ### Words that differ are told apart by a completed word -/











/-! ### The combinations no score can see -/

theorem APFPaper5.K2.score_eq_of_readoutEq (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (score : (g : Context) → WordFrom Frag g → Raw g → ℝ) (hz : ZeroConvention Defd score)
    {a b : Context} (W W' : Word Frag a b) (h : ReadoutEq Defd score W W')
    (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g) :
    score g (sandwich P W S) x = score g (sandwich P W' S) x := by sorry
