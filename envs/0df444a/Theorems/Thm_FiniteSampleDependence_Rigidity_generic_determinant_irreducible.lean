-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_generic_determinant_irreducible
-- name    : FiniteSampleDependence.Rigidity.generic_determinant_irreducible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:51:50.125056+00:00
-- url     : https://prove2.me/theorems/a03b5228-ddb4-4254-8d78-d210f4e65b17
-- title:
--   Lemma A.1 — the generic determinant is irreducible over $\mathbb R$
-- statement:
--   For every $n\ge1$, the determinant $\det(X_{ij})_{1\le i,j\le n}$ of the generic $n\times n$ matrix is an irreducible element of the polynomial ring $\mathbb R[X_{ij}:1\le i,j\le n]$.
--
--   Since this ring is a unique factorization domain, the generic determinant is prime; in the square case $n=m$ this is what removes the pivot factor in the proof of determinantal rigidity.
--
--   Differences from the source:
--   - encoding: variables U_{ij}, 1 ≤ i, j ≤ n → MvPolynomial (Fin n × Fin n) ℝ with the generic matrix Matrix.mvPolynomialX; reason: the same polynomial ring with zero-based indices
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Appendix A, Lemma A.1, PDF p. 23 (printed p. 22)

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_PolynomialAlgebra

namespace FiniteSampleDependence.Rigidity

/-- Lemma A.1 (Irreducibility of the generic determinant). For every `n ≥ 1`, the determinant of
the generic `n × n` matrix `(X_{ij})` is irreducible in `ℝ[X_{ij}]`. -/
theorem generic_determinant_irreducible (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (genericMatrix n n).det := by sorry

end FiniteSampleDependence.Rigidity
