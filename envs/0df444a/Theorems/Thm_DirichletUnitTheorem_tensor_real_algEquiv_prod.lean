-- Prove2me | Theorems.Thm_DirichletUnitTheorem_tensor_real_algEquiv_prod
-- name    : DirichletUnitTheorem.tensor_real_algEquiv_prod
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:32.728416+00:00
-- url     : https://prove2.me/theorems/c80c4211-3fd1-4dbc-8ebf-6d4ea951514b
-- title:
--   $K\otimes_{\mathbb Q}\mathbb R \cong \mathbb R^{r_1}\times\mathbb C^{r_2}$
-- statement:
--   Let $K$ be a number field. Then the tensor product $\mathbb R\otimes_{\mathbb Q}K$ decomposes as a product of fields, with $r_1$ copies of $\mathbb R$ and $r_2$ copies of $\mathbb C$:
--
--   $$\mathbb R\otimes_{\mathbb Q}K \;\cong\; \mathbb R^{r_1}\times\mathbb C^{r_2}$$
--
--   as $\mathbb R$-algebras. This is another characterization of the signature $(r_1,r_2)$.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), lead section, second bullet of "Other ways of determining r1 and r2".

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem tensor_real_algEquiv_prod (K : Type*) [Field K] [NumberField K] :
    Nonempty (TensorProduct ℚ ℝ K ≃ₐ[ℝ]
      ((Fin (InfinitePlace.nrRealPlaces K) → ℝ) × (Fin (InfinitePlace.nrComplexPlaces K) → ℂ))) := by sorry

end DirichletUnitTheorem
