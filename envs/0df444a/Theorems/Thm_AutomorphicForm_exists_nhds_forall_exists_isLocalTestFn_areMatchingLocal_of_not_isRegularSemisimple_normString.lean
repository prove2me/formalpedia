-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_not_isRegularSemisimple_normString
-- name    : AutomorphicForm.exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_not_isRegularSemisimple_normString
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/23d385dc-3b4c-5ed9-b829-fa7e44177dde
-- title:
--   Local transfer near an element with non-regular norm string
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $[L:K]=2$ or $3$, let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$, and let $v$ be a height one prime of $\mathcal{O}_K$ such that there is no $K$-algebra homomorphism $L \to K_v$, where $K_v$ is the $v$-adic completion. Let $\delta_0 \in \mathrm{GL}_2(L \otimes_K K_v)$ and assume that its norm string $\prod_{i<[L:K]} \sigma^{i}(\delta_0)$, formed with the automorphism of $\mathrm{GL}_2(L \otimes_K K_v)$ induced by $\sigma \otimes \mathrm{id}$, is not regular semisimple, i.e. $\mathrm{tr}^2 - 4\det$ of that product is not a unit. Then there is a set $U$ in the neighbourhood filter of $\delta_0$ with the following property: for every $\varphi_v : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ that is locally constant with compact support and satisfies $\mathrm{tsupport}\,\varphi_v \subseteq U$, there exists a locally constant, compactly supported $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ matching $\varphi_v$ in the following sense, with $\mu_L$ and $\mu_K$ the chosen Haar measures on $\mathrm{GL}_2(L \otimes_K K_v)$ and $\mathrm{GL}_2(K_v)$: first, whenever $\delta$ has regular semisimple norm string, $\gamma \in \mathrm{GL}_2(K_v)$ is regular semisimple, $y$ is a norm conjugator relating $\gamma$ and $\delta$, and Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the twisted centraliser of $\delta$ are coupled by $y$, any value $I'$ of the twisted orbital integral of $\varphi_v$ at $\delta$ against $\tau'$ equals any value $I$ of the orbital integral of $f_v$ at $\gamma$ against $\tau$; second, for every regular semisimple $\gamma$ that is not a norm and every Haar measure $\tau$ on its centraliser, every value of the orbital integral of $f_v$ at $\gamma$ against $\tau$ is $0$.
--
--   This is the local transfer (matching of orbital integrals with twisted orbital integrals) for cyclic base change of $\mathrm{GL}(2)$ at a place $v$ that does not split in $L$, in the case where the given point has a norm string failing regular semisimplicity; it corresponds to the singular-norm cases in Langlands' treatment. It is used, together with the regular semisimple case, in [`AutomorphicForm.exists_isLocalTestFn_areMatchingLocal_of_isEmpty_algHom`](thm.html#AutomorphicForm.exists_isLocalTestFn_areMatchingLocal_of_isEmpty_algHom) to produce a transfer for an arbitrary semi-local test function at such a place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_not_isRegularSemisimple_normString.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_not_isRegularSemisimple_normString
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K))
    (δ₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀ : ¬ AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ₀)) :
    ∃ U ∈ nhds δ₀, ∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      AutomorphicForm.IsSemiLocalTestFn K L v φv → tsupport φv ⊆ U →
        ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ,
          AutomorphicForm.IsLocalTestFn K v fv ∧ AutomorphicForm.AreMatchingLocal K L v σ φv fv := by sorry
