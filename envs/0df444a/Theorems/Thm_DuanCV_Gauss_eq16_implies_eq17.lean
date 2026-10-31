-- Prove2me | Theorems.Thm_DuanCV_Gauss_eq16_implies_eq17
-- name    : DuanCV.Gauss.eq16_implies_eq17
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:43.409252+00:00
-- url     : https://prove2.me/theorems/ff2a8e09-0d63-44a8-a97f-8b4a9e1251d3
-- title:
--   Eq. (16) with Eq. (11) yields Eq. (17)
-- statement:
--   Let $n_i,m_i,c_i$ be reals and $a_0>0$ with $a_0^4(n_i-1)=m_i-1$ for $i=1,2$, let
--
--   $$|c_1|-|c_2|=\sqrt{(n_1-1)(m_1-1)}-\sqrt{(n_2-1)(m_2-1)},$$
--
--   and suppose
--
--   $$a_0^2\,\frac{n_1+n_2}2+\frac{m_1+m_2}{2a_0^2}-|c_1|-|c_2|\ \ge\ a_0^2+\frac1{a_0^2}.$$
--
--   Then
--
--   $$|c_1|\le\sqrt{(n_1-1)(m_1-1)},\qquad |c_2|\le\sqrt{(n_2-1)(m_2-1)}.$$
--
--   This is the algebraic step that converts compliance with the bound into a condition on the entries of the covariance.
--
--   Differences from the source:
--   - encoding: Eq. (11) with a₀ from Theorem 2 → hypotheses a₀ > 0, a₀⁴(nᵢ−1) = mᵢ−1 and (11b); reason: the a₀ equations imply (11a) and the nonnegativity of the radicands
--   - generalization: nᵢ, mᵢ of a standard form II as produced by Lemma 2 → arbitrary real nᵢ, mᵢ, cᵢ, with either sign of nᵢ − 1 and any a₀ when nᵢ = mᵢ = 1; reason: the statement is real algebra; the paper's parameters are an instance
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Eqs. (16)–(17), p. 4

import Mathlib

namespace DuanCV.Gauss

/-- **Inequality (16) with Eq. (11) yields (17).**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Eqs. (16)–(17), p. 4.

Real algebra: for `a₀ > 0` with `a₀⁴(nᵢ - 1) = mᵢ - 1`, the identity (11b) and the inequality (16)
give `|cᵢ| ≤ √((nᵢ-1)(mᵢ-1))`.

**Formalization Note.** The equations `a₀⁴(nᵢ - 1) = mᵢ - 1` encode `a₀² = √((mᵢ-1)/(nᵢ-1))` without
division. They imply (11a) and the nonnegativity of the radicands. The sign of `nᵢ - 1` is free. -/
theorem eq16_implies_eq17 (n1 n2 m1 m2 c1 c2 a0 : ℝ) (ha0 : 0 < a0)
    (h1 : a0 ^ 4 * (n1 - 1) = m1 - 1) (h2 : a0 ^ 4 * (n2 - 1) = m2 - 1)
    (h11b : |c1| - |c2| =
      Real.sqrt ((n1 - 1) * (m1 - 1)) - Real.sqrt ((n2 - 1) * (m2 - 1)))
    (h16 : a0 ^ 2 + 1 / a0 ^ 2 ≤
      a0 ^ 2 * ((n1 + n2) / 2) + (m1 + m2) / (2 * a0 ^ 2) - |c1| - |c2|) :
    |c1| ≤ Real.sqrt ((n1 - 1) * (m1 - 1)) ∧ |c2| ≤ Real.sqrt ((n2 - 1) * (m2 - 1)) := by sorry

end DuanCV.Gauss
