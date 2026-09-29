-- Prove2me | Theorems.Thm_AutomorphicForm_exists_linearEquiv_twistedCommutant_tensor_mulVec_tmul_of_mul_map_mem_center_of_forall_ne_scalar
-- name    : AutomorphicForm.exists_linearEquiv_twistedCommutant_tensor_mulVec_tmul_of_mul_map_mem_center_of_forall_ne_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/b3ad2bca-87da-54da-a74c-b9a6759c1bc1
-- title:
--   Column map of a twisted commutant is an isomorphism after base change
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\operatorname{finrank}_K L = 2$, let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-algebra automorphism of $L$ lies in the subgroup of integer powers of $\sigma$, and let $\delta_0 \in \mathrm{GL}_2(L)$ satisfy: (i) $\delta_0 \cdot \sigma(\delta_0)$ lies in the centre of $\mathrm{GL}_2(L)$, where $\sigma$ acts entrywise; (ii) for no $x \in \mathrm{GL}_2(L)$ and $z \in L^\times$ is $x^{-1}\delta_0\,\sigma(x)$ the scalar matrix $z$. Let $b \in L^2$ be nonzero and let $A$ be any commutative ring with a $K$-algebra structure. Then there exist an $A$-submodule $D_A$ of $M_2(L \otimes_K A)$ — for the $A$-action through the right tensor factor — and an $A$-linear isomorphism $e \colon D_A \xrightarrow{\sim} (L \otimes_K A)^2$ such that $D_A$ is, as a set, $\{x \in M_2(L \otimes_K A) : x\,\delta_0^{(A)} = \delta_0^{(A)}\,(\sigma \otimes \mathrm{id}_A)(x)\}$, where $\delta_0^{(A)}$ is the image of $\delta_0$ under the entrywise map induced by $\ell \mapsto \ell \otimes 1$ and $(\sigma \otimes \mathrm{id}_A)$ is applied entrywise, and such that $e(x) = x \cdot (b_i \otimes 1)_i$ for every $x \in D_A$.
--
--   This is the statement that, for $\delta_0$ with central $\sigma$-norm and no scalar in its $\sigma$-conjugacy class, the twisted commutant $\{x : x\delta_0 = \delta_0\,\sigma(x)\}$ — a quaternion algebra over $K$ in the untwisted case $A = K$ — has its column map $x \mapsto xb$ an isomorphism onto $(L \otimes_K A)^2$ after an arbitrary base change to a commutative $K$-algebra $A$. It is the place-free algebraic core used at $A$ a completion $K_v$ and at the archimedean factor, and is cited in the construction of the level subgroup and in the archimedean estimates for the relevant automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_linearEquiv_twistedCommutant_tensor_mulVec_tmul_of_mul_map_mem_center_of_forall_ne_scalar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_linearEquiv_twistedCommutant_tensor_mulVec_tmul_of_mul_map_mem_center_of_forall_ne_scalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hδ₀ : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ ∈ Subgroup.center (GL (Fin 2) L))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (b : Fin 2 → L) (hb : b ≠ 0)
    (A : Type) [CommRing A] [Algebra K A] :
    ∃ (DA : Submodule A (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)))
      (e : DA ≃ₗ[A] (Fin 2 → L ⊗[K] A)),
      (DA : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) = {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) |
        x * ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ :
                GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
          ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ :
                GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
            x.map (AutomorphicForm.sigmaTensor K L A σ)} ∧
      ∀ x : DA, e x = (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).mulVec (fun i => b i ⊗ₜ[K] 1) := by sorry
