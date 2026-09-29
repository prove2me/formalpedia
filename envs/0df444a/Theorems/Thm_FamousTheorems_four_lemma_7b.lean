-- Prove2me | Theorems.Thm_FamousTheorems_four_lemma_7b
-- name    : FamousTheorems.four_lemma_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:56.68099+00:00
-- url     : https://prove2.me/theorems/62aec7e0-8d15-475f-9e07-83acaaa2e9e8
-- title:
--   The four lemma
-- statement:
--   **The four lemma.** Consider a commutative diagram of modules over a commutative ring
--   $$\begin{array}{ccccccc}M_1&\xrightarrow{f_1}&M_2&\xrightarrow{f_2}&M_3&\xrightarrow{f_3}&M_4\\\downarrow i_1&&\downarrow i_2&&\downarrow i_3&&\downarrow i_4\\N_1&\xrightarrow{g_1}&N_2&\xrightarrow{g_2}&N_3&\xrightarrow{g_3}&N_4\end{array}$$
--   with exact rows at $M_3$, $N_2$ and $N_3$. If $i_1$ and $i_3$ are surjective and $i_4$ is injective, then $i_2$ is surjective.
--
--   This is one half of the four lemma, and together with its dual it gives the five lemma: in a commutative diagram with exact rows, if the four outer vertical maps are isomorphisms, so is the middle one. These lemmas are basic tools of homological algebra, used to compare long exact sequences in homology and cohomology. The proof is a diagram chase.
--
--   **Formalization note.** Mathlib's `LinearMap.surjective_of_surjective_of_surjective_of_injective`. Commutativity of the squares is stated as equalities of composite linear maps, and `Function.Exact f g` says that the range of $f$ equals the kernel of $g$. Exactness of the top row at $M_2$ is not needed.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LinearMap.surjective_of_surjective_of_surjective_of_injective`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem four_lemma_7b {R M₁ M₂ M₃ M₄ N₁ N₂ N₃ N₄ : Type*} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄]
    [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄)
    (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (g₃ : N₃ →ₗ[R] N₄)
    (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) (i₃ : M₃ →ₗ[R] N₃) (i₄ : M₄ →ₗ[R] N₄)
    (hc₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (hc₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) (hc₃ : g₃ ∘ₗ i₃ = i₄ ∘ₗ f₃)
    (hf : Function.Exact f₂ f₃) (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃)
    (hi₁ : Function.Surjective i₁) (hi₃ : Function.Surjective i₃) (hi₄ : Function.Injective i₄) :
    Function.Surjective i₂ := by sorry

end FamousTheorems
