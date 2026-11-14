-- Prove2me | Theorems.Thm_BosonicLearn_displacementMatrix_mul
-- name    : BosonicLearn.displacementMatrix_mul
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T18:42:39.708057+00:00
-- url     : https://prove2.me/theorems/b64aec44-c9e6-43c0-8695-88b95eb1f96d
-- title:
--   Weyl relation for Fock matrix elements of displacements: $\sum_k D(a)_{mk}D(b)_{kn}=e^{(a\bar b-\bar a b)/2}D(a+b)_{mn}$
-- statement:
--   The Weyl (composition) relation for displacement operators, at the level of Fock matrix elements.
--
--   Let $D(z)_{mn}=\langle m|D(z)|n\rangle$, $D(z)=e^{za^\dagger-\bar za}$, be the Fock matrix elements of the single-mode displacement operator. For all $a,b\in\mathbb C$ and $m,n\in\mathbb N$,
--
--   $$
--   \sum_{k=0}^\infty D(a)_{mk}\,D(b)_{kn}=e^{(a\bar b-\bar ab)/2}\,D(a+b)_{mn},
--   $$
--
--   and the series converges absolutely.
--
--   Role. `IsGaussianState` is defined through the characteristic function $\chi_\rho(\xi)=\operatorname{Tr}[\rho D_\xi]$ built from these matrix elements. The Weyl relation is the first step of every argument that moves a state by a displacement (the proof of Theorem 8 uses that a common displacement does not change trace distances; existence of Gaussian states of arbitrary mean reduces to mean zero).
--
--   **Formalization Note** $D(z)_{mn}$ is the published normal-ordered formula `QAlgorithms.Papers.Independent.Dependency50.P39.displacementMatrix`, $e^{-|z|^2/2}\sqrt{m!n!}\sum_{j\le\min(m,n)}z^{m-j}(-\bar z)^{n-j}/(j!(m-j)!(n-j)!)$. The statement is a conjunction: `Summable` of the norms of the terms, and `HasSum` with the stated value.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, pp. 4–5 (displacement operators and characteristic function of an n-mode state); proof of Theorem 8, p. 62

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace BosonicLearn

/-- **Weyl relation for the Fock matrix elements of displacement operators.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, pp. 4–5 (quadratures, displacement and characteristic function of an n-mode state); proof of
Theorem 8, p. 62: "a common displacement is implemented by the same unitary on both states".

For `a, b ∈ ℂ` and Fock indices `m, n`, with `D(z)_{mn} = ⟨m|D(z)|n⟩`, `D(z) = exp(z a† − z̄ a)`,

`∑ₖ D(a)_{mk} D(b)_{kn} = exp((a b̄ − ā b)/2) · D(a + b)_{mn}`,

and the series converges absolutely.

**Formalization Note.** `D(z)_{mn}` is the published finite normal-ordered formula
`Dependency50.P39.displacementMatrix`, the matrix used by `IsGaussianState` through the Weyl kernel. -/
theorem displacementMatrix_mul (a b : ℂ) (m n : ℕ) :
    Summable (fun k : ℕ => ‖displacementMatrix a m k‖ * ‖displacementMatrix b k n‖) ∧
    HasSum (fun k : ℕ => displacementMatrix a m k * displacementMatrix b k n)
      (Complex.exp ((a * star b - star a * b) / 2) * displacementMatrix (a + b) m n) := by sorry

end BosonicLearn
