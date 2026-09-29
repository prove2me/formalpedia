-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuousLinearEquiv_twistedCommutant_tensor_adicCompletion_mulVec_of_forall_ne_scalar
-- name    : AutomorphicForm.exists_continuousLinearEquiv_twistedCommutant_tensor_adicCompletion_mulVec_of_forall_ne_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/660be62c-ee4b-5ce1-ac80-55897760693a
-- title:
--   Local twisted commutant: column map is a topological isomorphism
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\operatorname{finrank}_K L = 2$, let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-automorphism $\tau$ of $L$ lies in the group of integer powers of $\sigma$, and let $\delta_0 \in \mathrm{GL}_2(L)$ satisfy: $\delta_0 \cdot \mathrm{map}(\sigma)(\delta_0)$ lies in the centre of $\mathrm{GL}_2(L)$, and for no $x \in \mathrm{GL}_2(L)$ and $z \in L^\times$ is $x^{-1}\delta_0\,\mathrm{map}(\sigma)(x)$ the scalar matrix with entry $z$. Fix $b \colon \mathrm{Fin}\,2 \to L$ with $b \neq 0$ and a height-one prime $v$ of $\mathcal{O}_K$, and write $K_v$ for the $v$-adic completion of $K$. Then there are a $K_v$-submodule $D_v$ of $M_2(L \otimes_K K_v)$ and a continuous $K_v$-linear equivalence $e \colon D_v \simeq (L \otimes_K K_v)^2$ with continuous inverse such that, first, $D_v$ is, as a set, $\{x \in M_2(L \otimes_K K_v) \mid x\,\delta_0' = \delta_0'\,(\sigma \otimes \mathrm{id})(x)\}$, where $\delta_0'$ is the image of $\delta_0$ under the entrywise map induced by $L \to L \otimes_K K_v$, $\lambda \mapsto \lambda \otimes 1$, and $(\sigma \otimes \mathrm{id})$ is applied entrywise via the ring homomorphism [`AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ`](def/AutomorphicForm_TwistedOrbital.html#L199) given by $\sigma \otimes \mathrm{id}_{K_v}$ on $L \otimes_K K_v$; and second, $e(x) = x \cdot (b_i \otimes 1)_i$, the matrix–vector product of $x$ with the column vector $(b_i \otimes 1)_i$.
--
--   The local form of the column map on a twisted commutant: for a quadratic extension $L/K$ and a $\sigma$-twisted conjugacy datum $\delta_0$ with central norm and no $\sigma$-conjugate scalar form, the $K_v$-space $D_v$ of matrices satisfying $x\delta_0 = \delta_0\,\sigma(x)$ is carried isomorphically and homeomorphically onto $(L \otimes_K K_v)^2$ by $x \mapsto xb$. It is used in the choice of level for a test function on the adelic units of the associated algebra, where compactness and openness of the column image of a local order, and injectivity of the column map, are needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuousLinearEquiv_twistedCommutant_tensor_adicCompletion_mulVec_of_forall_ne_scalar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Topology

open scoped Classical

theorem AutomorphicForm.exists_continuousLinearEquiv_twistedCommutant_tensor_adicCompletion_mulVec_of_forall_ne_scalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hδ₀ : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ ∈ Subgroup.center (GL (Fin 2) L))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (b : Fin 2 → L) (hb : b ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ (Dv : Submodule (v.adicCompletion K) (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
      (e : Dv ≃L[v.adicCompletion K] (Fin 2 → L ⊗[K] v.adicCompletion K)),
      (Dv : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
        x * ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀ :
                GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀ :
                GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
            x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)} ∧
      ∀ x : Dv, e x = (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).mulVec (fun i => b i ⊗ₜ[K] 1) := by sorry
