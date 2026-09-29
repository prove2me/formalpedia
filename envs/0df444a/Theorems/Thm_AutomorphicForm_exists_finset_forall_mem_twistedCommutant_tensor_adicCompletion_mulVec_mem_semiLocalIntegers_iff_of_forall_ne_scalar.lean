-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_forall_mem_twistedCommutant_tensor_adicCompletion_mulVec_mem_semiLocalIntegers_iff_of_forall_ne_scalar
-- name    : AutomorphicForm.exists_finset_forall_mem_twistedCommutant_tensor_adicCompletion_mulVec_mem_semiLocalIntegers_iff_of_forall_ne_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/31f65eaf-c872-5bbf-a0df-f39b31450500
-- title:
--   Integrality of a column detects integrality in the local twisted commutant at almost all places
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ of degree $\operatorname{finrank}_K L = 2$, let $\sigma : L \simeq_{\mathrm{alg}[K]} L$ be such that every $K$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integral powers of $\sigma$, and let $\delta_0 \in \mathrm{GL}_2(L)$ satisfy: (i) $\delta_0 \cdot \sigma(\delta_0)$, the entrywise image of $\delta_0$ under $\sigma$ multiplied on the left by $\delta_0$, lies in the centre of $\mathrm{GL}_2(L)$; (ii) for no $x \in \mathrm{GL}_2(L)$ and $z \in L^\times$ does $x^{-1}\delta_0\,\sigma(x)$ equal the scalar matrix $z \cdot 1$. Let $b : \mathrm{Fin}\,2 \to L$ be a nonzero vector. Then there is a finite set $S$ of nonzero primes of $\mathcal{O}_K$ such that for every prime $v \notin S$ and every matrix $x \in M_2(L \otimes_K K_v)$, where $K_v$ is the $v$-adic completion, satisfying the twisted commutation relation $x \cdot \delta_0 = \delta_0 \cdot (\sigma \otimes \mathrm{id}_{K_v})(x)$ (with $\delta_0$ pushed into $M_2(L \otimes_K K_v)$ entrywise along $\ell \mapsto \ell \otimes 1$, and $\sigma \otimes \mathrm{id}$ applied entrywise), the following are equivalent: every coordinate of the vector $x \cdot (b \otimes 1)$ lies in the image of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_{K_v} \to L \otimes_K K_v$, and every entry $x_{ij}$ lies in that image.
--
--   This is the statement that, at all but finitely many finite places $v$ of $K$, the semi-local integral lattice in the local twisted commutant $D_v = \{x : x\delta_0 = \delta_0(\sigma\otimes 1)(x)\}$ is cut out by integrality of the single column $x \mapsto x(b\otimes 1)$; the non-scalar condition on $\delta_0$ is what makes the global twisted commutant a division algebra. It is the 'standard at almost all places' input to the choice of level, where the open compact subgroup is built as a product of column images of these lattices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_forall_mem_twistedCommutant_tensor_adicCompletion_mulVec_mem_semiLocalIntegers_iff_of_forall_ne_scalar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Topology

open scoped Classical

theorem AutomorphicForm.exists_finset_forall_mem_twistedCommutant_tensor_adicCompletion_mulVec_mem_semiLocalIntegers_iff_of_forall_ne_scalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hδ₀ : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ ∈ Subgroup.center (GL (Fin 2) L))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (b : Fin 2 → L) (hb : b ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ x ∈ {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
        x * ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀ :
                GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀ :
                GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
            x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)},
        (∀ i, (x.mulVec fun i => b i ⊗ₜ[K] (1 : v.adicCompletion K)) i ∈ AutomorphicForm.semiLocalIntegers K L v) ↔
          (∀ i j, x i j ∈ AutomorphicForm.semiLocalIntegers K L v) := by sorry
