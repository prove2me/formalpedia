-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_lemma_4_2
-- name    : CorrBoundsPoly.ExactDegree.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:20.255198+00:00
-- url     : https://prove2.me/theorems/967dab7a-afc2-4387-94d5-d8d8dbad90b1
-- title:
--   Lemma 4.2 — sum/product rules $\nu(f+g)=\nu(f)\nu(g)$, $\nu(fg)=1-(1-\nu(f))(1-\nu(g))/2$, and attainment
-- statement:
--   Let $f$ and $g$ be homogeneous polynomials of positive degrees $p$ and $q$ on disjoint sets of variables $\iota$ and $\kappa$ (written multilinearly). Then
--   1. if $p=q$, $\ \nu(f+g)=\nu(f)\,\nu(g)$; $\qquad(4.3)$
--   2. $$\nu(fg)=1-\frac{(1-\nu(f))(1-\nu(g))}{2}. \tag{4.4}$$
--   3. Moreover, if each certificate is attained by a polynomial correction of strictly smaller degree — there are Boolean functions $u$ on $\iota$ with $\deg u<p$ and $|\mathbb E(-1)^{f+u}|=\nu(f)$, and $v$ on $\kappa$ with $\deg v<q$ and $|\mathbb E(-1)^{g+v}|=\nu(g)$ — then the sum certificate (when $p=q$) is attained by a correction of degree below $p$, and the product certificate by a correction of degree below $p+q$: there are $w$ with $|\mathbb E(-1)^{f+g+w}|=\nu(f+g)$, resp. $|\mathbb E(-1)^{fg+w}|=\nu(fg)$.
--
--   These rules propagate the certificate $\nu$ and its attainment through the recursion (4.6) defining the exact-degree cores (Lemma 4.3).
--
--   Differences from the source:
--   - encoding: disjoint variables → `f` on `ι`, `g` on `κ`, renamed into `ι ⊕ κ`; reason: relabelling
--   - encoding: $f,g$ as elements of $A$ → multilinear polynomials (`IsMultilinear`); reason: the basis $x_S$ of $A$ and the paper's multilinear representation of Boolean polynomials
--   - reading: "homogeneous positive-degree" → `IsHomogeneous` of degree `p ≥ 1` (resp. `q ≥ 1`), which also admits the zero polynomial; reason: Mathlib's convention; at $0$ all three assertions hold with $\nu(0)=1$ and a constant correction
--   - reading: "attained by a polynomial correction of strictly smaller degree" → a Boolean function $u$ with `HasDegLE u (p - 1)` and bias $|\mathbb E(-1)^{f+u}|=\nu(f)$; reason: the proof's "signed bias $+\nu(f)$ (adjusting constants if needed)": adding the constant $1$ flips the sign without changing the degree bound
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 31 (PDF 33), Lemma 4.2, Eqs. (4.3), (4.4)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_Rho
import Definitions.Def_CorrBoundsPoly_ExactDegree_TruncAlg

namespace CorrBoundsPoly.ExactDegree

/-- **Lemma 4.2** (Sum/product certificates and their attainment; Xin Li, *More on Correlation
Bounds for Polynomials*, p. 31, PDF 33). Let `f` (on variables `ι`) and `g` (on variables `κ`) be
homogeneous of positive degrees `p`, `q`, on disjoint variables. Then (1) if `p = q`,
`ν(f + g) = ν(f) ν(g)` (Eq. (4.3)); (2) `ν(fg) = 1 − (1 − ν(f))(1 − ν(g))/2` (Eq. (4.4));
(3) if each certificate is attained by a correction of strictly smaller degree
(`|E(−1)^{f+u}| = ν(f)` with `deg u < p`, `|E(−1)^{g+v}| = ν(g)` with `deg v < q`), then so are
the sum certificate (when `p = q`, by a correction of degree `< p`) and the product certificate (by
a correction of degree `< p + q`). -/
theorem lemma_4_2 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : MvPolynomial ι (ZMod 2)) (g : MvPolynomial κ (ZMod 2)) (p q : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hfm : IsMultilinear f) (hgm : IsMultilinear g)
    (hf : f.IsHomogeneous p) (hg : g.IsHomogeneous q) :
    (p = q →
      nu (MvPolynomial.rename Sum.inl f + MvPolynomial.rename Sum.inr g) = nu f * nu g) ∧
    nu (MvPolynomial.rename Sum.inl f * MvPolynomial.rename Sum.inr g) =
      1 - (1 - nu f) * (1 - nu g) / 2 ∧
    ((∃ u : BoolFn ι, HasDegLE u (p - 1) ∧ bias (evalFn f + u) = nu f) →
      (∃ v : BoolFn κ, HasDegLE v (q - 1) ∧ bias (evalFn g + v) = nu g) →
      (p = q → ∃ w : BoolFn (ι ⊕ κ), HasDegLE w (p - 1) ∧
        bias (evalFn (MvPolynomial.rename Sum.inl f + MvPolynomial.rename Sum.inr g) + w) =
          nu (MvPolynomial.rename Sum.inl f + MvPolynomial.rename Sum.inr g)) ∧
      (∃ w : BoolFn (ι ⊕ κ), HasDegLE w (p + q - 1) ∧
        bias (evalFn (MvPolynomial.rename Sum.inl f * MvPolynomial.rename Sum.inr g) + w) =
          nu (MvPolynomial.rename Sum.inl f * MvPolynomial.rename Sum.inr g))) := by sorry

end CorrBoundsPoly.ExactDegree
