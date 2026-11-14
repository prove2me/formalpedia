-- Prove2me | Theorems.Thm_BosonicLearn_displacementMatrix_prod_mul
-- name    : BosonicLearn.displacementMatrix_prod_mul
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T18:47:19.788633+00:00
-- url     : https://prove2.me/theorems/2f97934b-367d-44d2-91f0-edf34b0bb130
-- title:
--   Weyl relation for multi-mode displacement kernels: $\sum_w D(a)_{uw}D(b)_{wv}=\prod_j e^{(a_j\bar b_j-\bar a_jb_j)/2}D(a_j+b_j)_{u_jv_j}$
-- statement:
--   The Weyl relation for products of single-mode displacements over a finite set of modes.
--
--   Let $I$ be a finite set of modes, $a,b\in\mathbb C^I$, and for occupation vectors $u,w\in\mathbb N^I$ let $D(a)_{uw}=\prod_{j\in I}D(a_j)_{u_jw_j}$. Then
--
--   $$
--   \sum_{w\in\mathbb N^I}D(a)_{uw}\,D(b)_{wv}=\prod_{j\in I}e^{(a_j\bar b_j-\bar a_jb_j)/2}\,D(a_j+b_j)_{u_jv_j},
--   $$
--
--   and the sum over $\mathbb N^I$ converges absolutely.
--
--   Role. The product over modes is the Weyl kernel used in the definition of `IsGaussianState` (`Support50.P14.oscillatorWeylKernel`), so this is the composition law of the $n$-mode displacement operators $D_\xi$.
--
--   **Formalization Note** $D(z)_{mn}$ is `Dependency50.P39.displacementMatrix`; `I` is any `Fintype`. The statement is a conjunction of `Summable` (product of the norms of the two kernels) and `HasSum`. Proved from `BosonicLearn.displacementMatrix_mul`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, pp. 4–5 (displacement operators and characteristic function of an n-mode state); proof of Theorem 8, p. 62

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace BosonicLearn

/-- **Weyl relation for multi-mode displacement kernels.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, pp. 4–5 (n-mode quadratures and displacements); proof of Theorem 8, p. 62: "a common displacement is
implemented by the same unitary on both states".

For a finite set `I` of modes, amplitudes `a, b : I → ℂ` and occupation vectors `u, v : I → ℕ`, with
`D(a)_{uw} = ∏ⱼ D(aⱼ)_{uⱼ wⱼ}`,

`∑_w D(a)_{uw} D(b)_{wv} = ∏ⱼ exp((aⱼ b̄ⱼ − āⱼ bⱼ)/2) · D(aⱼ + bⱼ)_{uⱼ vⱼ}`,

the sum over all `w : I → ℕ` converging absolutely.

**Formalization Note.** `D(z)_{mn}` is `Dependency50.P39.displacementMatrix`; the product over modes is the
form of the Weyl kernel `Support50.P14.oscillatorWeylKernel` used by `IsGaussianState`. -/
theorem displacementMatrix_prod_mul {I : Type} [Fintype I] (a b : I → ℂ) (u v : I → ℕ) :
    Summable (fun w : I → ℕ => ‖∏ j, displacementMatrix (a j) (u j) (w j)‖ *
      ‖∏ j, displacementMatrix (b j) (w j) (v j)‖) ∧
    HasSum (fun w : I → ℕ => (∏ j, displacementMatrix (a j) (u j) (w j)) *
        ∏ j, displacementMatrix (b j) (w j) (v j))
      (∏ j, Complex.exp ((a j * star (b j) - star (a j) * b j) / 2) *
        displacementMatrix (a j + b j) (u j) (v j)) := by sorry

end BosonicLearn
