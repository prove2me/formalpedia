-- Prove2me | Theorems.Thm_ConleyZehnder_signature_eq_zero_of_hyperbolic
-- name    : ConleyZehnder.signature_eq_zero_of_hyperbolic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T23:25:36.882633+00:00
-- url     : https://prove2.me/theorems/09bba6bb-ccfb-46d7-aada-03a0f2bf3982
-- title:
--   A Cayley-type matrix of a hyperbolic symplectic matrix has signature zero
-- statement:
--   Let $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ and let $A\in\mathrm{Sp}(2n)$, $AJ_0A^{T}=J_0$, be a real symplectic matrix with no eigenvalue on the unit circle $\{z\in\mathbb C:|z|=1\}$. Then $\pm1$ are not eigenvalues of $A$, the matrix
--   $$N=J_0\,(A-\mathrm{Id})\,(A+\mathrm{Id})^{-1}$$
--   is symmetric and invertible, and
--   $$\mathrm{Sign}(N)=0,$$
--   that is, $N$ has exactly $n$ positive and $n$ negative eigenvalues, counted with multiplicity.
--
--   Hyperbolic symplectic matrices arise as linearized return maps of nondegenerate hyperbolic periodic orbits. The statement shows that the symmetric matrix $N$ attached to such a matrix carries no signature. Together with the index formula `czIndex_two_mul_eq_neg_signature`, it gives the zero property of the Conley–Zehnder index (Gutt, Proposition 8 (3)).
--
--   Formalization note: `signature`, `J₀`, `IsSymplectic` and `Mat n` come from the definition module `ConleyZehnder_Setting`; `signature` counts positive minus negative eigenvalues. "No eigenvalue on the unit circle" is stated over $\mathbb C$ as `(A.map ofReal - z • 1).det ≠ 0` for all `‖z‖ = 1`. Since `signature` takes a proof that its argument is symmetric, that proof is passed as the hypothesis `hN`.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (3) (zero); signature statement new lemma of this mission

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- If a symplectic matrix `A` has no eigenvalue on the unit circle, then the symmetric matrix
`J₀ (A - Id) (A + Id)⁻¹` has signature `0`. -/
theorem signature_eq_zero_of_hyperbolic {n : ℕ} (A : Mat n) (hA : IsSymplectic A)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (A.map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0)
    (hN : (J₀ n * (A - 1) * (A + 1)⁻¹).IsHermitian) :
    signature (J₀ n * (A - 1) * (A + 1)⁻¹) hN = 0 := by sorry

end ConleyZehnder
