-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime
-- name    : AutomorphicForm.exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/0848650b-1141-595e-9cc7-26d475e3e591
-- title:
--   Adelic norms from local norms in prime-degree base change
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, assume the degree $\operatorname{finrank}_K L$ is a prime number, and let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$. Let $\gamma \in \mathrm{GL}_2(\mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring `AdeleRing (𝓞 K) K`, and suppose $\gamma$ is regular semisimple in the sense of [`AutomorphicForm.IsRegularSemisimple`](def/AutomorphicForm_LocalOrbitalBase.html#L402), namely that $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of $\mathbb{A}_K$. Here, for a commutative $K$-algebra $A$, an element $\gamma' \in \mathrm{GL}_2(A)$ is a norm of $\delta \in \mathrm{GL}_2(L \otimes_K A)$ (the predicate [`AutomorphicForm.IsNormOf`](def/AutomorphicForm_TwistedOrbital.html#L217)) when the base change `toTensorGL` of $\gamma'$ to $\mathrm{GL}_2(L \otimes_K A)$ equals $y^{-1} \cdot \mathrm{normString}_{K,L,A,\sigma}(\delta) \cdot y$ for some $y \in \mathrm{GL}_2(L \otimes_K A)$. Assume: for every height-one prime $v$ of $\mathcal{O}_K$, the $v$-component of the finite-adelic part of $\gamma$ (obtained by `AdelicLevel.glFin` followed by `AdelicLevel.finComponent`) is a norm of some $\delta_v \in \mathrm{GL}_2(L \otimes_K K_v)$; and the archimedean part `AdelicLevel.glArch` of $\gamma$ is a norm of some $\delta_\infty \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$. Then $\gamma$ is a norm of some $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$.
--
--   This is the globalisation step in cyclic base change of prime degree: being a norm locally everywhere, for a regular semisimple adelic element, implies being a norm adelically, the content being integrality at almost all finite places. It cites the local statement that an integral element with unit discriminant at a place unramified in $L$ lies in the image of the norm string, and is used in the results matching adelic orbital integrals from local matching at every place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.exists_isNormOf_adeleRing_of_forall_exists_isNormOf_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) δv)
    (harch : ∃ δa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K γ) δa) :
    ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ γ δ := by sorry
