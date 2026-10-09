-- Prove2me | Theorems.Thm_CurvatureSubmod_CSSP_condNum_sq_ge
-- name    : CurvatureSubmod.CSSP.condNum_sq_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:59:04.888993+00:00
-- url     : https://prove2.me/theorems/79fa805d-6705-40c6-85b1-742f7d23ecc4
-- title:
--   Proof of Lemma 8.2, p. 12 — κ²(A) ≥ f^A_∅(i)/f^A_{[n]−i}(i) for each i ∈ [n]
-- statement:
--   Let $A$ be a real $m \times n$ matrix with linearly independent columns $c_1, \dots, c_n$, let $f^A$ be the column-subset selection objective, and let $\kappa(A) = \sup_{\|x\|=1}\|Ax\| / \inf_{\|x\|=1}\|Ax\|$ be its condition number. Then for each $i \in [n]$,
--   $$\frac{f^A_\emptyset(i)}{f^A_{[n]-i}(i)} \le \kappa^2(A) .$$
--
--   Both marginal values are negative, so the left side is the ratio of their absolute values. The denominator is nonzero because, under independence, $c_i$ is not in the span of the other columns. This is the inequality from which the curvature bound of Lemma 8.2 is read off.
--
--   **Formalization Note** The quotient is real division. Independence of the columns (the page's "non-singular") makes the denominator strictly negative, so Lean's convention $x/0 = 0$ never applies.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 12, proof of Lemma 8.2, last paragraph

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting

namespace CurvatureSubmod.CSSP

/-- Proof of Lemma 8.2, p. 12, conclusion: for independent columns,
`κ²(A) ≥ f^A_∅(i) / f^A_{[n]−i}(i)` for each `i ∈ [n]` (the denominator is `< 0`). -/
theorem condNum_sq_ge {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m))
    (hc : LinearIndependent ℝ c) (i : Fin n) :
    marg (fA c) ∅ i / marg (fA c) (Finset.univ.erase i) i ≤ condNum c ^ 2 := by sorry

end CurvatureSubmod.CSSP
