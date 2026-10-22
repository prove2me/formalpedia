-- Prove2me | Theorems.Thm_CycBMWFree_Freeness_sum_squares_updown
-- name    : CycBMWFree.Freeness.sum_squares_updown
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:51.430051+00:00
-- url     : https://prove2.me/theorems/aa42b366-0d9c-4368-b3fa-6833422fab1d
-- title:
--   Proof of Theorem 5.2, p. 44 — tableau sum of squares
-- statement:
--   For $r\ge1$ and $n\ge0$, let $Γ_n$ be the allowed shapes and $T(n,λ)$ the up–down tableaux. Their squared counts add to the cyclotomic Brauer rank:
--   $$
--   \sum_{λ\in Γ_n}|T(n,λ)|^2=r^n(2n-1)!!.
--   $$
--   The identity identifies the dimension of the split generic algebra. **Formalization Note** Lean counts pairs of tableaux in a dependent sum; its cardinality is the displayed sum. The paper derives this equality by comparison with the $\mathbb Z_r$-Brauer algebra.
-- source:
--   Goodman & Hauschild Mosley, Cyclotomic BMW algebras II, arXiv:math/0612065v5, p. 44, proof of Theorem 5.2

import Mathlib
import Definitions.Def_CycBMWFree_Freeness_Setting

noncomputable section
open scoped BigOperators

namespace CycBMWFree.Freeness
open QAlgorithms.Papers.Independent.Support21.P14

/-- The tableau-count identity in the proof of Theorem 5.2, p. 44. -/
theorem sum_squares_updown (r n : ℕ) (hr : 0 < r) :
    Nat.card (Σ la : Gamma r n, UpDown r n la.1 × UpDown r n la.1) = rankN r n := by sorry

end CycBMWFree.Freeness
