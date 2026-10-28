-- Prove2me | Theorems.Thm_D1Bound5_pellMatchingCheck_sound
-- name    : D1Bound5.pellMatchingCheck_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:38:12.94288+00:00
-- url     : https://prove2.me/theorems/5cdb507a-2ea4-487c-ae2b-8b5b071eb0fd
-- title:
--   Pell Matching Check sound
-- statement:
--   Auxiliary result `pellMatchingCheck_sound` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PellMatchingCheck.lean, lines 114-134, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions

section
namespace D1Bound5





























theorem _root_.D1Bound5.pellMatchingCheck_sound (d : ℤ) (ms : List PellSquareMasks)
    (hvalid : ∀ m ∈ ms, m.Valid d) (xs : List ℤ)
    (wss : List (List (ℕ × ℕ))) (hcheck : pellMatchingCheck ms xs wss = true)
    (x y : ℤ) (hx : x ∈ xs) (hy : y ∈ xs) (hne : x ≠ y) :
    (¬∃ r : ℤ, r*r = x*y+1) ∧ (¬∃ r : ℤ, d*r*r = x*y-1) := by sorry















end D1Bound5
end
