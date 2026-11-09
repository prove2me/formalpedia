-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_gram_determinant_monotone
-- name    : FiniteSampleDependence.Rigidity.gram_determinant_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:52:17.884646+00:00
-- url     : https://prove2.me/theorems/ec0dafb5-654f-475b-a0e8-ceb0d7485121
-- title:
--   Proposition 4.4 — the Gram determinant $\det(UU^\top)$ is a degree-$2n$ monotone
-- statement:
--   Let $2\le n\le m$. The polynomial $F_{\mathrm{Gram}}(U)=\det(UU^\top)$ in the entries of $U$
--
--   1. is nonzero: it is a nonzero polynomial and it takes a nonzero value at some $U\in\Delta_{n,m}$;
--   2. has total degree exactly $2n$;
--   3. satisfies (LF-DPI) on $\Delta_{n,m}$;
--   4. satisfies (IZ) on $\Delta_{n,m}$.
--
--   It shows that the degree bound $2n$ of determinantal rigidity is attained for every $2\le n\le m$.
--
--   Differences from the source:
--   - reading: 'is nonzero' → both: nonzero as a polynomial, and nonzero at some point of Δ_{n,m}; reason: the source's proof shows positivity at a simplex point, which gives both readings; stating both covers either reading
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: the polynomial F_Gram(U) and its degree → the element gramPoly n m of MvPolynomial (Fin n × Fin m) ℝ, evaluated at U by polyFun, with degree MvPolynomial.totalDegree; reason: polyFun_gramPoly proves that its value at U is det(UU^⊤); same polynomial and same total degree
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Proposition 4.4, PDF p. 14 (printed p. 13)

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_PolynomialAlgebra

namespace FiniteSampleDependence.Rigidity

/-- Proposition 4.4 (Gram-determinant monotone). For `2 ≤ n ≤ m`, the polynomial
`F_Gram(U) = det(U Uᵀ)` is nonzero (as a polynomial, and indeed at some point of the simplex),
has total degree exactly `2n`, and satisfies (LF-DPI) and (IZ) on `Δ_{n,m}`. -/
theorem gram_determinant_monotone {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    gramPoly n m ≠ 0 ∧
    (∃ U ∈ simplex n m, polyFun (gramPoly n m) U ≠ 0) ∧
    (gramPoly n m).totalDegree = 2 * n ∧
    LFDPI (polyFun (gramPoly n m)) ∧
    IZ (polyFun (gramPoly n m)) := by sorry

end FiniteSampleDependence.Rigidity
