-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_lemma_2_1
-- name    : CorrBoundsPoly.ExactDegree.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:57:56.977702+00:00
-- url     : https://prove2.me/theorems/31c3c8b7-0ab5-4a28-b4e8-5eeb16270ddc
-- title:
--   Lemma 2.1 — rank does not increase on taking a symbol
-- statement:
--   Let $(F_s)_{s\in\mathbb Q}$ be a finite rationally indexed filtration of the Boolean function algebra $B$ on $m$ variables, with associated graded space $\operatorname{gr}_F=\bigoplus_s F_s/F_{s-}$. If a linear operator $A:B\to B$ has shift at most $D\in\mathbb Q$ (that is, $AF_s\subseteq F_{s+D}$ for all $s$) and degree-$D$ symbol $T=\operatorname{gr}_D(A)$, then
--   $$\operatorname{rank}A\ \ge\ \operatorname{rank}T .$$
--
--   This is the step that transfers rank lower bounds from the leading operator to every lower-degree perturbation of a multiplication operator in the leading-rank criterion (Theorem 2.3).
--
--   **Formalization Note** Ranks are the cardinal ranks `LinearMap.rank`. The filtration is any `RatFiltration (ZMod 2) (BFun m)` (coordinate compatibility is not needed here, as on the page).
--
--   Differences from the source:
--   - encoding: $B=\mathbb F_2[x]/(x_i^2-x_i)$ → `BFun m`, functions $\mathbb F_2^m\to\mathbb F_2$ with pointwise operations; reason: the paper identifies $B$ with these functions by evaluation (p. 26)
--   - encoding: rank of $A$ and of $T$ → cardinal rank `LinearMap.rank`; reason: equals the dimension of the image
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 20 (PDF 22), Lemma 2.1

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_Filtration

namespace CorrBoundsPoly.ExactDegree

/-- **Lemma 2.1** (Xin Li, *More on Correlation Bounds for Polynomials*, p. 20, PDF 22). Let `Φ` be a
finite rationally indexed filtration of the Boolean function algebra `B` on `m` variables. If a
linear operator `A : B → B` has shift at most `D` and degree-`D` symbol `T = gr_D(A)`, then
`rank A ≥ rank T`. Ranks are cardinal ranks of the images. -/
theorem lemma_2_1 (m : ℕ) (Φ : RatFiltration (ZMod 2) (BFun m)) (A : BFun m →ₗ[ZMod 2] BFun m)
    (D : ℚ) (hA : Φ.HasShiftLE A D) :
    LinearMap.rank (Φ.symbol A D hA) ≤ LinearMap.rank A := by sorry

end CorrBoundsPoly.ExactDegree
