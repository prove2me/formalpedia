-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ThreePairSignatureSchur_three_pair_signature_schur
-- name    : CountingMatroid.Analysis.ThreePairSignatureSchur.three_pair_signature_schur
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T08:55:59.411776+00:00
-- url     : https://prove2.me/theorems/ebb210e6-ce1d-4933-88e7-131f99cd5c9d
-- title:
--   Schur bound from a single positive direction
-- statement:
--   Let $a,c,d,e,z$ be rational numbers with $c>0$, and let
--
--   $$H=\begin{pmatrix}2a&z&2d\\z&2c&2e\\2d&2e&0\end{pmatrix}.$$
--
--   Suppose that the quadratic form associated with $H$ has positive index at most one: every subspace on which it is positive definite has dimension at most one. Then, for every pair of rational numbers $x,y$,
--
--   $$2c\bigl(2ax^2+4dxy\bigr)\leq(zx+2ey)^2.$$
--
--   This is the negative-semidefiniteness bound for the Schur complement of the positive entry $2c$. It supplies the elementary signature step used in the proof of the three-pair defect-weight inequality in Lemma 3.2. No sign hypothesis on $a,d,e,z$ is required.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ThreePairSignatureSchur.lean#L23-L95 — three_pair_signature_schur; paper Lemma 3.2, p. 6, Schur-complement step following (8).

import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

set_option autoImplicit false

/-!
The real quadratic signature implies the rational Schur-complement bound
used by the operational three-pair partition comparison.
-/

namespace CountingMatroid.Analysis.ThreePairSignatureSchur
end CountingMatroid.Analysis.ThreePairSignatureSchur
open CountingMatroid.Analysis.ThreePairSignatureSchur

open scoped Matrix

theorem CountingMatroid.Analysis.ThreePairSignatureSchur.three_pair_signature_schur (a c d e z : ℚ) (hc : 0 < c)
    (hsig : sigPos (threePairMatrix a c d e z).toQuadraticForm' ≤ 1) :
    ∀ x y : ℚ, 2 * c * (2 * a * x ^ 2 + 4 * d * x * y) ≤
      (z * x + 2 * e * y) ^ 2 := by sorry
