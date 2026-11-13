-- Prove2me | Theorems.Thm_AaronsonAmbainis_Short_det_core
-- name    : AaronsonAmbainis.Short.det_core
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-12T07:41:07.978258+00:00
-- url     : https://prove2.me/theorems/632bbf20-cebc-4393-adb4-8e7c7f379fc3
-- title:
--   Determinant inequality on a cube: marked antipodal pairs number at most $\sum_i w_i b_i$
-- statement:
--   Let $g:\{0,1\}^J\to\{0,1\}$, $X_1=g^{-1}(1)$, and let $b_i$ be the number of edges in direction $i$ with one endpoint in $X_1$. Let $w\in\mathbb R^J_{\ge 0}$. Let $P\subseteq X_1$ and for each $x\in P$ let $K_x\subseteq J$ satisfy, with $y=x^J$ the antipode of $x$:
--
--   1. $x^S\in X_1$ for every $S\subseteq K_x$;
--   2. every $z\in X_1$ that differs from $x$ on all of $K_x$ has $w(\Delta(y,z))\ge 1$.
--
--   Then $|P|\le\sum_{i\in J}w_ib_i$.
--
--   The proof takes the matrix $M_{xz}=\prod_{i:x_i=z_i}t_i$ on $X_1$, whose determinant is nonzero, and compares a minimal monomial of $\det M$ under two families of row operations.
-- source:
--   Huffstutler, Miloschewsky and Podder, A short proof of the Aaronson-Ambainis Conjecture via the completion framework, arXiv:2611.12795, proof of Lemma 4, Eq. (4); after Turturean, A proof of the Aaronson-Ambainis conjecture, arXiv:2611.09773, Section 3.

import Definitions.Def_AaronsonAmbainis_Short
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.Short.det_core {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → Bool) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (P : Finset (Cube ι)) (K : Cube ι → Finset ι)
    (hwing : ∀ x ∈ P, ∀ S : Finset ι, S ⊆ K x → g (flipSet x S) = true)
    (hfar : ∀ x ∈ P, ∀ z : Cube ι, g z = true → K x ⊆ diffSet x z →
      1 ≤ ∑ i ∈ diffSet (antipode x) z, w i) :
    (P.card : ℝ) ≤ ∑ i, w i * (bdry g i : ℝ) := by sorry
