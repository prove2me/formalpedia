-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_determinantal_rigidity_full
-- name    : FiniteSampleDependence.Rigidity.determinantal_rigidity_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:52:41.192195+00:00
-- url     : https://prove2.me/theorems/660d3590-172a-42c6-ae99-113325d86c13
-- title:
--   Theorem B — determinantal rigidity: $F\in I_n^2+(\tau-1)$, $\deg F\ge 2n$, attained by $\det(UU^\top)$, and $F=(\det U)^2G$ when $n=m$
-- statement:
--   Let $2\le n\le m$, let $R_{n,m}=\mathbb R[U_{i\alpha}]$, let $I_n$ be the ideal of maximal minors of the generic $n\times m$ matrix and $\tau=\sum_{i,\alpha}U_{i\alpha}$.
--
--   1. Every polynomial $F\in R_{n,m}$ whose functional on $\Delta_{n,m}$ satisfies (LF-DPI) and (IZ) obeys
--   $$F\in I_n^2+(\tau-1).$$
--   2. If moreover $F$ is not identically zero on $\Delta_{n,m}$, then $\deg F\ge 2n$ (total degree of this polynomial, for every representative).
--   3. The bound is attained by $F_{\mathrm{Gram}}(U)=\det(UU^\top)$: it is nonzero at some point of $\Delta_{n,m}$, has degree exactly $2n$, and satisfies (LF-DPI) and (IZ).
--   4. If $n=m$, then for every polynomial $F\in R_{n,n}$ satisfying (LF-DPI) and (IZ) on $\Delta_{n,n}$ there is a polynomial $G\in R_{n,n}$ with
--   $$F(U)=(\det U)^2\,G(U)\qquad\text{for all }U\in\Delta_{n,n}.$$
--
--   Combined with the polynomial characterization of fixed-sample unbiased estimability, this says that a nontrivial polynomial dependence measure obeying the data processing inequality needs at least $2n$ samples, and that this is sharp.
--
--   Differences from the source:
--   - encoding: the attainment clause 'The bound is attained by det(UU^⊤)' → the Gram polynomial det(XX^⊤) is nonzero at a simplex point, has total degree 2n, and satisfies (LF-DPI) and (IZ); reason: this is what attaining the bound means: an admissible polynomial, nonzero on the simplex, of degree exactly 2n
--   - encoding: the square-case sentence 'For n = m, ...' about the same F → a fourth conjunct, under n = m, quantifying over polynomials in the n×n entries; reason: when n = m the n×m and n×n polynomial rings coincide; stating it over R_{n,n} avoids a type cast
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: n-element column sets S ⊆ [m] → strictly increasing maps Fin n → Fin m; reason: an n-subset listed in increasing order; same set of minors
--   - encoding: a real polynomial F in the entries U_{iα}, its value F(U), and its degree deg F → an element of MvPolynomial (Fin n × Fin m) ℝ, evaluated at U by polyFun, with degree MvPolynomial.totalDegree; reason: the same polynomial ring, evaluation and total degree; totalDegree 0 = 0 never enters, because the degree clause assumes a nonzero value on the simplex
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Theorem B, PDF p. 4 (printed p. 3); Theorem 4.1, PDF p. 11 (printed p. 10); square case Section 4.4 and Corollary 4.5, PDF p. 14 (printed p. 13)

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_PolynomialAlgebra

namespace FiniteSampleDependence.Rigidity

/-- Theorem B (determinantal rigidity), with Theorem 4.1 and the square specialization.
Let `2 ≤ n ≤ m`. Every real polynomial `F` in the `nm` matrix entries whose functional on
`Δ_{n,m}` satisfies (LF-DPI) and (IZ) lies in `I_n² + (τ − 1)`; if it is not identically zero on
`Δ_{n,m}`, then its total degree is at least `2n`. The bound is attained by
`F_Gram = det(X Xᵀ)`. For `n = m`, every such `F` satisfies `F(U) = (det U)² G(U)` on the
simplex for some polynomial `G`. -/
theorem determinantal_rigidity_full {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    (∀ F : PolyRing n m, LFDPI (polyFun F) → IZ (polyFun F) →
      F ∈ maxMinorIdeal n m ^ 2 ⊔ simplexIdeal n m ∧
      ((∃ U ∈ simplex n m, polyFun F U ≠ 0) → 2 * n ≤ F.totalDegree)) ∧
    ((∃ U ∈ simplex n m, polyFun (gramPoly n m) U ≠ 0) ∧
      (gramPoly n m).totalDegree = 2 * n ∧
      LFDPI (polyFun (gramPoly n m)) ∧ IZ (polyFun (gramPoly n m))) ∧
    (n = m → ∀ F : PolyRing n n, LFDPI (polyFun F) → IZ (polyFun F) →
      ∃ G : PolyRing n n, ∀ U ∈ simplex n n, polyFun F U = U.det ^ 2 * polyFun G U) := by sorry

end FiniteSampleDependence.Rigidity
