-- Prove2me | Theorems.Thm_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext
-- name    : AutomorphicForm.exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/2440f55f-9d4a-59d4-bccf-25ae57b2005c
-- title:
--   Prescribing components of GL₂(L⊗_KA_K)
-- statement:
--   Let $K$ and $L$ be number fields with $L$ given as an algebra over $K$. The assertion is the conjunction of an existence and a uniqueness statement for the component maps of $\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring of $\mathcal{O}_K$ in $K$ and the component maps are those induced on $\mathrm{GL}_2$ by the algebra homomorphisms $\mathrm{id}_L\otimes(\text{archimedean projection})$ and $\mathrm{id}_L\otimes(\text{projection to the }v\text{-adic completion})$, namely [`AutomorphicForm.tensorArch K L`](def/AutomorphicForm_BaseChangePlaces.html#L46) into $\mathrm{GL}_2(L\otimes_K K_\infty)$ and [`AutomorphicForm.tensorPlace K L v`](def/AutomorphicForm_BaseChangePlaces.html#L49) into $\mathrm{GL}_2(L\otimes_K K_v)$ for $v$ in the height one spectrum of $\mathcal{O}_K$. Existence: for every finite set $S$ of height one primes of $\mathcal{O}_K$, every $x_\infty\in\mathrm{GL}_2(L\otimes_K K_\infty)$ and every family $(x_v)_v$ with $x_v\in\mathrm{GL}_2(L\otimes_K K_v)$, such that for all $v\notin S$ the element $x_v$ lies in [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136), i.e. both $x_v$ and $x_v^{-1}$ have all matrix entries in the image of the semi-local integers $\mathcal{O}_L\otimes\mathcal{O}_{K_v}$ under `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v`, there exists $x\in\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ whose archimedean component is $x_\infty$ and whose component at every $v$ is $x_v$. Uniqueness: two elements of $\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ with the same archimedean component and the same component at every height one prime are equal.
--
--   This is the restricted-product description of $\mathrm{GL}_2$ over the base-changed adele ring $L\otimes_K\mathbb{A}_K$: components at the archimedean place and at all finite places, almost all semi-locally integral, may be prescribed independently and determine the global element. It is used when assembling twisted torus families of adelic elements from locally specified data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    (∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (xa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
        (xv : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
        (∀ v ∉ S, xv v ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
        ∃ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          AutomorphicForm.tensorArch K L x = xa ∧
          ∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.tensorPlace K L v x = xv v) ∧
    (∀ x x' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
        AutomorphicForm.tensorArch K L x = AutomorphicForm.tensorArch K L x' →
        (∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.tensorPlace K L v x = AutomorphicForm.tensorPlace K L v x') →
          x = x') := by sorry
