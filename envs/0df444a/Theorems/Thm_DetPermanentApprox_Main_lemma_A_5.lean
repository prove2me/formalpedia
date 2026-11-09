-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_A_5
-- name    : DetPermanentApprox.Main.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:31:46.82918+00:00
-- url     : https://prove2.me/theorems/a30de1fb-8ec5-4443-9c3e-637728b04f5e
-- title:
--   Lemma A.5 — Monomial, magnitude and denominator bounds
-- statement:
--   For the actual polynomial $U$ and rounded matrix $C$ in Algorithm 2, let $u_jw^{\gamma_j}$ range over the distinct nonzero monomials, let $S$ be their count, and set $a_j=u_j\prod_e C_e^{(\gamma_j)_e}$ and $(b_j)_v=\sum_{e\ni v}(\gamma_j)_e$. With $H_U=m(2(n^2+1))^m$ and $D_U=m!(4K)^m(4K+1)^m(8K+1)^m$,
--
--   $$1\le S\le(n^2+1)^m,\quad |a_j|\le H_U,\quad 0\le(b_j)_v\le m,\quad |b_j\cdot\theta|\le2mR_0\quad(\theta\in X).$$
--
--   The reduced denominators of $u_j$ divide $D_U$, and those of $a_j$ divide $D_U2^{pm}$. The parameters make $K$ an integer; the general-graph surrogate theorem does not assume that. These are bounds on the constructed coefficients, not arbitrary coefficient promises.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: monomials indexed from 1 to S and nonnegative integer b_j coordinates → the support subtype of the actual rational polynomial, with natural-valued b_j; reason: each distinct nonzero monomial occurs once; nonnegativity is enforced by the coordinate type and no instance changes
--   - generalization: C and p produced by Algorithm 1 preprocessing → any rational C and natural p satisfying RoundedData, with the same Section 4 parameters; reason: every source output satisfies RoundedData; the arguments on pp.21-30 use only its entry, grid, permanent and support properties, without the construction history or the least choice of p
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma A.5, p. 26 (PDF p. 26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Numerical
import Definitions.Def_DetPermanentApprox_Main_Analysis

namespace DetPermanentApprox.Main

theorem lemma_A_5 {n : ℕ} (hn : 2 ≤ n) (C : Matrix (Fin n) (Fin n) ℚ)
    (p s : ℕ) (hs : 2 ≤ s) (hC : RoundedData C p) :
    1 ≤ monomialCount C s ∧ monomialCount C s ≤ (n ^ 2 + 1) ^ matrixDegree s ∧
    (∀ j : Monomial C s, |coefficientA C s j| ≤ (coefficientHeight n s : ℚ) ∧
      (∀ v, coefficientB C s j v ≤ matrixDegree s) ∧
      (∀ θ ∈ box n p s,
        |∑ v, (coefficientB C s j v : ℝ) * θ v| ≤
          2 * matrixDegree s * (boxRadius n p s : ℝ)) ∧
      ((matrixSurrogate C s).coeff j.val).den ∣ denominatorBound s ∧
      (coefficientA C s j).den ∣ denominatorBound s * 2 ^ (p * matrixDegree s)) := by sorry

end DetPermanentApprox.Main
