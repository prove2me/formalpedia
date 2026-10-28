-- Prove2me | Theorems.Thm_D1Bound5_pellMatchingCheck_no_three
-- name    : D1Bound5.pellMatchingCheck_no_three
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:41:46.252008+00:00
-- url     : https://prove2.me/theorems/2040ac0d-36eb-4ab7-95b5-73ed6f85b0ee
-- title:
--   Pell Matching Check no three
-- statement:
--   The graph certificate proves a matching, a stronger property than the triangle exclusion needed by the article. No huge integer square roots are trusted or executed by this checker.
-- source:
--   D1Bound5/PellMatchingCheck.lean, lines 170-191, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions

section
namespace D1Bound5






































theorem _root_.D1Bound5.pellMatchingCheck_no_three (d : ℤ) (hd : 0 < d)
    (ms : List PellSquareMasks) (hvalid : ∀ m ∈ ms, m.Valid d)
    (xs : List ℤ) (wss : List (List (ℕ × ℕ)))
    (hcheck : pellMatchingCheck ms xs wss = true)
    (hlarge : ∀ x ∈ xs, 2 ≤ x)
    (a b c : ℤ) (ha : PellSignedMember xs a) (hb : PellSignedMember xs b)
    (hc : PellSignedMember xs c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsab : PellIntegerSquare d (a*b+1))
    (hsac : PellIntegerSquare d (a*c+1)) : False := by sorry







end D1Bound5
end
