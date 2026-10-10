-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_two_mul_eq_neg_signature
-- name    : ConleyZehnder.czIndex_two_mul_eq_neg_signature
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T23:12:48.670288+00:00
-- url     : https://prove2.me/theorems/962af583-f6c3-486d-bea6-a9ac9ef68c59
-- title:
--   Conley–Zehnder index of a path avoiding the eigenvalue −1
-- statement:
--   Let $\mathrm{SP}(n)$ be the set of continuous paths $\psi:[0,1]\to\mathrm{Sp}(2n)$ with $\psi(0)=\mathrm{Id}$ and $\det(\mathrm{Id}-\psi(1))\neq 0$ (Gutt, Definition 4), let $\mu_{CZ}$ be the Conley–Zehnder index (Gutt, Definition 7 and Corollary 12), and let $\mathrm{Sign}$ denote the signature of a symmetric matrix (number of positive minus number of negative eigenvalues, with multiplicity).
--
--   Let $\psi\in\mathrm{SP}(n)$ be such that $-1$ is not an eigenvalue of $\psi(t)$ for any $t\in[0,1]$. Then the matrix
--   $$N=J_0\,(\psi(1)-\mathrm{Id})\,(\psi(1)+\mathrm{Id})^{-1}$$
--   is symmetric and
--   $$2\,\mu_{CZ}(\psi)=-\,\mathrm{Sign}(N).$$
--
--   The statement computes the index of every path that never meets the eigenvalue $-1$ from its endpoint alone. Examples are short paths, and paths with no eigenvalue on the unit circle for $t>0$ (Gutt, Proposition 8 (3)). It is also compatible with the signature normalization (Gutt, Proposition 8 (6)).
--
--   Formalization note: `SP`, `czIndex`, `signature`, `J₀` and `Mat n` come from the definition module `ConleyZehnder_Setting`; `Matrix.J` is $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ and the symplectic group is $AJ_0A^{T}=J_0$. "No eigenvalue $-1$" is `(1 + ψ t).det ≠ 0`. Since `signature` takes a proof that its argument is symmetric (`IsHermitian` over `ℝ`), that proof is passed as the hypothesis `hN`; the value of `signature` does not depend on it.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239); index formula for paths avoiding the eigenvalue -1 (new lemma of this mission)

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- If `ψ ∈ SP(n)` and no `ψ(t)` has the eigenvalue `-1`, then the Conley–Zehnder index is
`μ_CZ(ψ) = -½ Sign(J₀ (ψ(1) - Id) (ψ(1) + Id)⁻¹)`; the matrix `J₀ (ψ(1) - Id) (ψ(1) + Id)⁻¹` is
symmetric. -/
theorem czIndex_two_mul_eq_neg_signature {n : ℕ} (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n)
    (hneg : ∀ t, (1 + ψ t).det ≠ 0)
    (hN : (J₀ n * (ψ 1 - 1) * (ψ 1 + 1)⁻¹).IsHermitian) :
    2 * czIndex ψ = -signature (J₀ n * (ψ 1 - 1) * (ψ 1 + 1)⁻¹) hN := by sorry

end ConleyZehnder
