-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_lemma_3_3
-- name    : CorrBoundsPoly.ExactDegree.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:01.98442+00:00
-- url     : https://prove2.me/theorems/222688ed-9720-430c-8d3e-a0e362a1a379
-- title:
--   Lemma 3.3 — $|\mathbb E(-1)^F|\le2^{-n}h(f)$ for the leading homogeneous part $f$ of $F$
-- statement:
--   Let $F\in B_n$ have degree $D\ge1$, written as a multilinear polynomial, and let $f$ be its **leading homogeneous part** (the sum of its monomials of degree $D$). With $h(f)=2^n-2\operatorname{rank}_{A_n}\mu_f$ computed in the truncated algebra $A_n=\mathbb F_2[x]/(x_i^2)$,
--   $$\big|\mathbb E\,(-1)^{F}\big|\le2^{-n}h(f). \tag{3.5}$$
--   In particular, the same bound holds for $F=f+P$ whenever $f$ is homogeneous of degree $D$ and $\deg P<D$.
--
--   Applied to $F=f+P$ for every test $P$ of degree below $D$, this bounds $\rho_{D-1}(f)$ by the normalized rank defect $\nu(f)=2^{-n}h(f)$.
--
--   Differences from the source:
--   - encoding: $F\in B_n$ of degree $D$ with leading homogeneous part $f$ → a multilinear polynomial `F` with `totalDegree F = D` and `f = homogeneousComponent D F`; reason: the multilinear representative is unique and its degree is $\deg F$
--   - encoding: $\deg P<D$ → `HasDegLE P (D - 1)` with `1 ≤ D`; reason: same condition for $D\ge1$
--   - encoding: $f$ in the "in particular" clause → a multilinear homogeneous polynomial of degree $D$; reason: the leading part of a Boolean polynomial written multilinearly
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 27 (PDF 29), Lemma 3.3, Eq. (3.5)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_Rho
import Definitions.Def_CorrBoundsPoly_ExactDegree_TruncAlg

namespace CorrBoundsPoly.ExactDegree

/-- **Lemma 3.3** (Leading homogeneous part; Xin Li, *More on Correlation Bounds for Polynomials*,
p. 27, PDF 29). (1) If `F ∈ B_n` (written multilinearly) has degree `D ≥ 1` and leading
homogeneous part `f` (its degree-`D` component), then `|E(−1)^F| ≤ 2^{−n} h(f)` (Eq. (3.5)), `h`
computed in the truncated algebra `A_n`. (2) In particular the same bound holds for `F = f + P`
whenever `f` is homogeneous of degree `D` and `deg P < D`. -/
theorem lemma_3_3 (n D : ℕ) (hD : 1 ≤ D) :
    (∀ F : MvPolynomial (Fin n) (ZMod 2), IsMultilinear F → F.totalDegree = D →
      bias (evalFn F) ≤ (hA (MvPolynomial.homogeneousComponent D F) : ℝ) / 2 ^ n) ∧
    (∀ (f : MvPolynomial (Fin n) (ZMod 2)) (P : BoolFn (Fin n)), IsMultilinear f →
      f.IsHomogeneous D → HasDegLE P (D - 1) →
      bias (evalFn f + P) ≤ (hA f : ℝ) / 2 ^ n) := by sorry

end CorrBoundsPoly.ExactDegree
