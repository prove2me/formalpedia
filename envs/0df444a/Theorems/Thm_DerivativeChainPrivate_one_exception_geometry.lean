-- Prove2me | Theorems.Thm_DerivativeChainPrivate_one_exception_geometry
-- name    : DerivativeChainPrivate.one_exception_geometry
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:57:34.308429+00:00
-- url     : https://prove2.me/theorems/ba087be9-f9de-4a2e-9aa3-4c697179e6cf
-- title:
--   Two extremal candidate costs across one exceptional transition
-- statement:
--   For real a,l,r,L,R,U,V with l<=a<=r, L<=R, U>=-1, l>=-1, r<=1, V<=1, the minimum of a-l+|L-l|+L-U and r-a+|R-r|+V-R is at most 3. This proves the candidate-cost inequality, not the existence of the root chains used in its application.
-- source:
--   Derivative-zero chains: public formalization reference, R37, DerivativeChainPrivate.one_exception_geometry. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.one_exception_geometry (a l r L R U V : ℝ)
    (hl : l ≤ a) (hr : a ≤ r) (hLR : L ≤ R)
    (hU : -1 ≤ U) (hl1 : -1 ≤ l) (hr1 : r ≤ 1) (hV : V ≤ 1) :
    min (a - l + |L - l| + L - U) (r - a + |R - r| + V - R) ≤ 3 := by sorry
