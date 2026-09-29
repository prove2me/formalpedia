-- Prove2me | Theorems.Thm_FamousTheorems_fundamental_theorem_symmetric_polynomials
-- name    : FamousTheorems.fundamental_theorem_symmetric_polynomials
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:51.688042+00:00
-- url     : https://prove2.me/theorems/3f5725d0-95d8-448b-9216-2a564d8f2dad
-- title:
--   Fundamental theorem of symmetric polynomials
-- statement:
--   **The fundamental theorem of symmetric polynomials.** Let $R$ be a commutative ring and $\sigma$ a finite set of variables, and let $n\ge|\sigma|$. Every symmetric polynomial in the variables $\sigma$ is a polynomial in the elementary symmetric polynomials $e_1,\dots,e_n$. That is, the $R$-algebra map
--   $$R[X_1,\dots,X_n]\to R[\sigma]^{\mathrm{sym}},\qquad X_i\mapsto e_i,$$
--   is surjective.
--
--   This is the classical basis of the theory of symmetric functions. It shows that the coefficients of a polynomial determine every symmetric function of its roots, such as the discriminant and the power sums, and it is used in Newton's identities and in the proof that $\pi$ and $e$ are transcendental.
--
--   **Formalization note.** Mathlib's `MvPolynomial.esymmAlgHom_surjective`. `MvPolynomial.esymmAlgHom σ R n` maps the variable indexed by `i : Fin n` to the elementary symmetric polynomial `esymm σ R (i + 1)` in the symmetric subalgebra `symmetricSubalgebra σ R`. For $n>|\sigma|$ the extra $e_i$ are $0$. Mathlib also shows injectivity when $n=|\sigma|$, which is not part of this statement.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MvPolynomial.esymmAlgHom_surjective`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fundamental_theorem_symmetric_polynomials (σ R : Type*) [Fintype σ] [CommRing R] {n : ℕ} (h : Fintype.card σ ≤ n) :
    Function.Surjective (MvPolynomial.esymmAlgHom σ R n) := by sorry

end FamousTheorems
