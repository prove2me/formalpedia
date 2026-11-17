-- Prove2me | Theorems.Thm_APFPaper5_K2_told_apart_by_admitted_word
-- name    : APFPaper5.K2.told_apart_by_admitted_word
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:46:35.539425+00:00
-- url     : https://prove2.me/theorems/25718303-078a-403b-a2db-fa061f94b89d
-- title:
--   told apart by admitted word
-- statement:
--   Result: told apart by admitted word. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem told_apart_by_admitted_word {R : Context → Type uR}
--       (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
--       (resource : (g : Context) → WordFrom Frag g → R g)
--       (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
--       (value : (g : Context) → WordFrom Frag g → Raw g → Val)
--       {a b : Context} (W W' : Word Frag a b)
--       (h : ¬ ReadoutEq (Cont step resource calibration C) value W W') :
--       ∃ (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g),
--         ((∃ y : Raw c, Executes step (P.append (W.append S)) x y) ∧
--             calibration g (resource g (sandwich P W S)) ≤ C g) ∨
--         ((∃ y : Raw c, Executes step (P.append (W'.append S)) x y) ∧
--             calibration g (resource g (sandwich P W' S)) ≤ C g)
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
--   ['Theorems.Thm_APFPaper5_K2_closed_boundary_on_words:246; pullbacks v39; source SHA-256 53befb18d62f4f7ca23091d8275015586b7d38d3cc263a68544f0abab264b9e5']

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

theorem APFPaper5.K2.told_apart_by_admitted_word {R : Context → Type uR}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b : Context} (W W' : Word Frag a b)
    (h : ¬ ReadoutEq (Cont step resource calibration C) value W W') :
    ∃ (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g),
      ((∃ y : Raw c, Executes step (P.append (W.append S)) x y) ∧
          calibration g (resource g (sandwich P W S)) ≤ C g) ∨
      ((∃ y : Raw c, Executes step (P.append (W'.append S)) x y) ∧
          calibration g (resource g (sandwich P W' S)) ≤ C g) := by sorry
