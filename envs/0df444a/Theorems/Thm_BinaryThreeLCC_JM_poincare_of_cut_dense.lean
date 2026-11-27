-- Prove2me | Theorems.Thm_BinaryThreeLCC_JM_poincare_of_cut_dense
-- name    : BinaryThreeLCC.JM.poincare_of_cut_dense
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:02:23.632187+00:00
-- url     : https://prove2.me/theorems/434b553a-0b70-503c-9c8c-55877a479521
-- title:
--   Poincaré inequality from cut density
-- statement:
--   Let $\Omega$ be a finite set with $m=|\Omega|$ elements and let $w:\Omega\times\Omega\to[0,\infty)$ be weights whose row sums and column sums are at most $D$. Let $\kappa\ge0$ and suppose $w$ is $\kappa$-cut-dense:
--
--   $$\sum_{i\in S}\ \sum_{j\in\Omega\setminus S} w(i,j)\ \ge\ \kappa\,|S|\,|\Omega\setminus S|\qquad\text{for every }S\subseteq\Omega .$$
--
--   Then every $h:\Omega\to\mathbb R$ with $\sum_i h(i)=0$ satisfies
--
--   $$\frac{\kappa^2 m^2}{4D}\sum_{i} h(i)^2\ \le\ \sum_{i,j} w(i,j)\,\bigl(h(i)-h(j)\bigr)^2 .$$
--
--   This is the spectral-gap input of the mixing argument (the source derives it from Cheeger's inequality); here it is stated directly as a Poincaré inequality for the Dirichlet form, with the convention that the left side is $0$ when $D=0$.
-- source:
--   Janzer–Manohar, Reed–Muller Codes are Optimal Binary Linear 3-Query LCCs, STOC 2027 submission #732, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf, Proposition 5.5(5) and Fact 3.6 (printed pp. 9, 14–15); quadratic-form substitute for the Cheeger step

import Mathlib

set_option autoImplicit false

namespace BinaryThreeLCC.JM

theorem poincare_of_cut_dense {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (wt : Ω → Ω → ℝ) (hw : ∀ i j, 0 ≤ wt i j) (D : ℝ)
    (hrow : ∀ i, ∑ j, wt i j ≤ D) (hcol : ∀ j, ∑ i, wt i j ≤ D)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hcut : ∀ S : Finset Ω, κ * S.card * (Finset.univ \ S).card ≤
      ∑ i ∈ S, ∑ j ∈ Finset.univ \ S, wt i j)
    (h : Ω → ℝ) (hsum : ∑ i, h i = 0) :
    κ ^ 2 * (Fintype.card Ω : ℝ) ^ 2 / (4 * D) * ∑ i, h i ^ 2 ≤
      ∑ i, ∑ j, wt i j * (h i - h j) ^ 2 := by sorry

end BinaryThreeLCC.JM
