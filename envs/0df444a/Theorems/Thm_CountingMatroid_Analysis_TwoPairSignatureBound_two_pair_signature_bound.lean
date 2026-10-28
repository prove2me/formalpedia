-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_TwoPairSignatureBound_two_pair_signature_bound
-- name    : CountingMatroid.Analysis.TwoPairSignatureBound.two_pair_signature_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T09:44:48.803826+00:00
-- url     : https://prove2.me/theorems/c35254e7-5e38-4a5f-a11f-e96a40ceddfb
-- title:
--   Two-pair determinant bound from a single positive direction
-- statement:
--   Let $a,c,z$ be rational numbers with $a>0$, and consider the real symmetric matrix
--
--   $$H=\begin{pmatrix}2a&z\\z&2c\end{pmatrix}.$$
--
--   If the quadratic form $u\mapsto u^{\mathsf T}Hu$ has positive index at most one, then
--
--   $$4ca\leq z^2.$$
--
--   Equivalently, $\det H\leq0$. There is no sign assumption on $c$ or $z$. This is the elementary signature step used for the two-pair inequality in Lemma 3.2 of the counting paper; identifying the coefficients with matroid partition weights requires separate lemmas.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/TwoPairSignatureBound.lean#L16-L46 — two_pair_signature_bound; the quadratic-form argument used in the proof of Lemma 3.2, p. 6.

import Definitions.Def_CountingMatroid_Analysis_TwoPairSignatureBound
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

set_option autoImplicit false

/-! The elementary determinant consequence of the two-pair Hessian signature. -/

namespace CountingMatroid.Analysis.TwoPairSignatureBound
end CountingMatroid.Analysis.TwoPairSignatureBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.TwoPairSignatureBound

open scoped Matrix

theorem CountingMatroid.Analysis.TwoPairSignatureBound.two_pair_signature_bound (a c z : ℚ) (ha : 0 < a)
    (hsig : sigPos (twoPairMatrix a c z).toQuadraticForm' ≤ 1) :
    4 * c * a ≤ z ^ 2 := by sorry
