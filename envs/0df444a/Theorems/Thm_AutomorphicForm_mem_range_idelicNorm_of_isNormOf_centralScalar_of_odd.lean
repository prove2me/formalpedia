-- Prove2me | Theorems.Thm_AutomorphicForm_mem_range_idelicNorm_of_isNormOf_centralScalar_of_odd
-- name    : AutomorphicForm.mem_range_idelicNorm_of_isNormOf_centralScalar_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/106b9f58-0e80-5e0d-9740-c557bf16ca97
-- title:
--   Twisted norm of a scalar idele in odd-degree cyclic descent
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite-dimensional $K$-algebra, the extension $L/K$ being Galois, and suppose the degree $\operatorname{finrank}_K L$ is odd. Let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $\tau \in \operatorname{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, so that the Galois group is cyclic with generator $\sigma$. Let $u$ be a unit of the adele ring $\mathbb{A}_K$ of $K$ (an idele of $K$), and write $\operatorname{centralScalar}(u) = u \cdot I_2$ for the associated central scalar element of $\mathrm{GL}_2(\mathbb{A}_K)$, namely the image of $u$ under `Matrix.GeneralLinearGroup.scalar (Fin 2)`. Assume there is a $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ for which $\operatorname{centralScalar}(u)$ is a norm of $\delta$ in the sense of [`AutomorphicForm.IsNormOf`](def/AutomorphicForm_TwistedOrbital.html#L217), that is, there exists $y \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ with $$\mathrm{toTensorGL}\bigl(u \cdot I_2\bigr) = y^{-1} \cdot \mathrm{normString}\,\sigma\,\delta \cdot y,$$ where [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) is the base-change map $\mathrm{GL}_2(\mathbb{A}_K) \to \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ and $\mathrm{normString}\,\sigma\,\delta$ is the $\sigma$-twisted norm string of $\delta$. The conclusion is that $u$ lies in the range of the monoid homomorphism $(\mathbb{A}_L)^\times \to (\mathbb{A}_K)^\times$ attached to the adele base change [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87), i.e. of `Units.map` applied to the algebra norm of $\mathbb{A}_L$ over $\mathbb{A}_K$ along the ring homomorphism $\mathbb{A}_K \to \mathbb{A}_L$ of that base change; thus $u = N_{L/K}(w)$ for some idele $w$ of $L$.
--
--   This is the norm-recognition step in cyclic base change for $\mathrm{GL}_2$ in odd degree: a central scalar idele which is a twisted norm in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ is already an idelic norm from $L$, the oddness of the degree removing the ambiguity coming from determinants. It is used in the comparison of twisted orbital integrals with orbital integrals at central elements, via [`AutomorphicForm.finsum_sigmaCentralizerDomain_centralNorm_eq_mul_sum_finsum_centralizerDomain_central_of_central_transfer`](thm.html#AutomorphicForm.finsum_sigmaCentralizerDomain_centralNorm_eq_mul_sum_finsum_centralizerDomain_central_of_central_transfer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_range_idelicNorm_of_isNormOf_centralScalar_of_odd.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct

theorem AutomorphicForm.mem_range_idelicNorm_of_isNormOf_centralScalar_of_odd
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hodd : Odd (Module.finrank K L))
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (h : ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K u) δ) :
    u ∈ (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range := by sorry
