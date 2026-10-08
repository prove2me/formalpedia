-- Prove2me | Theorems.Thm_AlgebraicPCSP_OneInThree_lemma_8_8
-- name    : AlgebraicPCSP.OneInThree.lemma_8_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:18.629202+00:00
-- url     : https://prove2.me/theorems/9e3ea84a-c376-4ff7-bb0b-dd7c96c2210c
-- title:
--   Lemma 8.8 — the operation t is cyclic
-- statement:
--   Let $s:D^p\to D$ be a cyclic operation and let $t$ be the $p^2$-ary operation
--   $$t(x_{11},x_{12},\dots,x_{1p},x_{21},\dots,x_{pp})=s\big(s(x_{11},\dots,x_{p1}),\dots,s(x_{1p},\dots,x_{pp})\big).$$
--   Then $t$ is cyclic as an operation of its $p^2$ arguments in the order $(x_{11},x_{12},\dots,x_{1p},x_{21},\dots,x_{pp})$:
--   $$t(x_{12},\dots,x_{pp},x_{11})=t(x_{11},x_{12},\dots,x_{pp}).$$
--
--   Cyclicity of $t$ lets the proof replace a tuple $\langle i\rangle$ by any cyclic shift of it without changing $t$, which is how covers are built from line segments in Lemma 8.9.
--
--   **Formalization Note** Stated for every $p$ and every type $D$; only cyclicity of $s$ is assumed. The argument tuple is read into a matrix row-major via `finProdFinEquiv`.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 54, Lemma 8.8

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices

namespace AlgebraicPCSP.OneInThree

/-- Lemma 8.8 (p. 54): if `s` is cyclic, then the `p²`-ary operation `t`, taken on its
arguments in row-major order `(x₁₁, x₁₂, …, x₁ₚ, x₂₁, …, x_pp)`, is cyclic. -/
theorem lemma_8_8 {D : Type} {p : ℕ} (s : (Fin p → D) → D) (hcyc : IsCyclic s) :
    IsCyclic (tFlat s) := by sorry

end AlgebraicPCSP.OneInThree
