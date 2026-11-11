-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_lemma_3_4
-- name    : CorrBoundsPoly.ExactDegree.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:06.214744+00:00
-- url     : https://prove2.me/theorems/a9c03c8c-5d74-4bef-ad97-b1570e87f655
-- title:
--   Lemma 3.4 — disjoint sums multiply the rank defect: $h(f+g)=h(f)h(g)$, $\nu(f+g)=\nu(f)\nu(g)$
-- statement:
--   Let $f$ and $g$ be homogeneous of the same positive degree $p$, on disjoint sets of variables $\iota$ and $\kappa$ (elements of the truncated algebras $A_\iota$, $A_\kappa$, written multilinearly). Viewing $f+g$ in $A_{\iota\sqcup\kappa}$,
--   $$h(f+g)=h(f)\,h(g),\qquad\text{equivalently}\qquad \nu(f+g)=\nu(f)\,\nu(g).$$
--
--   This is the tensor identity of Lemma 2.2 for multiplication operators in the truncated algebra, and it is the sum rule (4.3) of the recursion for the exact-degree cores.
--
--   Differences from the source:
--   - encoding: disjoint variables → `f` on `ι`, `g` on `κ`, both renamed into `ι ⊕ κ` (`Sum.inl`, `Sum.inr`); reason: relabelling
--   - encoding: elements of $A$ → multilinear polynomials (`IsMultilinear`); reason: the basis $x_S$ of $A$
--   - reading: "homogeneous of positive degree" → `IsHomogeneous p` with `1 ≤ p`, which also admits the zero polynomial; reason: Mathlib's convention; at $f=0$ or $g=0$ both sides agree ($\nu(0)=1$, $h(0)$ is the dimension)
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 27 (PDF 29), Lemma 3.4

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_TruncAlg

namespace CorrBoundsPoly.ExactDegree

/-- **Lemma 3.4** (Disjoint sums; Xin Li, *More on Correlation Bounds for Polynomials*, p. 27,
PDF 29). For homogeneous `f`, `g` of the same positive degree `p` on disjoint variable sets `ι`
and `κ` (elements of the truncated algebras, written multilinearly), `h(f + g) = h(f) h(g)`;
equivalently `ν(f + g) = ν(f) ν(g)`. -/
theorem lemma_3_4 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : MvPolynomial ι (ZMod 2)) (g : MvPolynomial κ (ZMod 2)) (p : ℕ) (hp : 1 ≤ p)
    (hfm : IsMultilinear f) (hgm : IsMultilinear g)
    (hf : f.IsHomogeneous p) (hg : g.IsHomogeneous p) :
    hA (MvPolynomial.rename Sum.inl f + MvPolynomial.rename Sum.inr g) = hA f * hA g ∧
      nu (MvPolynomial.rename Sum.inl f + MvPolynomial.rename Sum.inr g) = nu f * nu g := by sorry

end CorrBoundsPoly.ExactDegree
