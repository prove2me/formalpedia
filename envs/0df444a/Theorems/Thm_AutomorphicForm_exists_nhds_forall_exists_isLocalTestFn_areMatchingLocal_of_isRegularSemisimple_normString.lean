-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_isRegularSemisimple_normString
-- name    : AutomorphicForm.exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_isRegularSemisimple_normString
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/b57ae1d0-10ca-56a5-91b5-59faedb218de
-- title:
--   Local transfer near δ₀ with regular semisimple norm string
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\dim_K L = 2$ or $3$, let $\sigma$ be a $K$-automorphism of $L$ with $\sigma \neq 1$, and let $v$ be a nonzero prime of $\mathcal{O}_K$ such that there is no $K$-algebra homomorphism $L \to K_v$, where $K_v$ denotes the $v$-adic completion. Let $\delta_0 \in \mathrm{GL}_2(L \otimes_K K_v)$ be such that its norm string $\prod_{i<\dim_K L} \sigma_{\mathrm{GL}}^{i}(\delta_0)$, formed with the automorphism $\sigma_{\mathrm{GL}}$ of $\mathrm{GL}_2(L \otimes_K K_v)$ induced by $\sigma \otimes \mathrm{id}$, is regular semisimple in the sense that $\mathrm{tr}^2 - 4\det$ of it is a unit. Then $\delta_0$ has a neighbourhood $U$ with the following property: for every $\varphi_v : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ that is locally constant with compact support and satisfies $\mathrm{tsupport}\,\varphi_v \subseteq U$, there is a locally constant, compactly supported $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ matching $\varphi_v$ locally, i.e. (i) whenever $\delta$ has regular semisimple norm string, $\gamma \in \mathrm{GL}_2(K_v)$ is regular semisimple, $y$ is a norm conjugator from $\gamma$ to $\delta$, and $\tau$, $\tau'$ are Haar measures on the centraliser of $\gamma$ and on the $\sigma$-twisted centraliser of $\delta$ coupled through $y$, then any value of the $\sigma$-twisted orbital integral of $\varphi_v$ at $\delta$ against $\tau'$ and the semilocal Haar measure equals any value of the orbital integral of $f_v$ at $\gamma$ against $\tau$ and the local Haar measure; and (ii) for regular semisimple $\gamma$ that is not a norm of any $\delta$, every value of the orbital integral of $f_v$ at $\gamma$ against any Haar measure on its centraliser is $0$.
--
--   This is the local matching (transfer) of test functions at a place $v$ of $K$ that does not split in $L$, in the form needed for cyclic base change for $\mathrm{GL}(2)$: test functions supported near a fixed $\delta_0$ with regular semisimple norm string admit a transfer to $\mathrm{GL}_2(K_v)$. It is the local ingredient of [`AutomorphicForm.exists_isLocalTestFn_areMatchingLocal_of_isEmpty_algHom`](thm.html#AutomorphicForm.exists_isLocalTestFn_areMatchingLocal_of_isEmpty_algHom), which removes the support restriction at such a place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_isRegularSemisimple_normString.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_isRegularSemisimple_normString
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K))
    (δ₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ₀)) :
    ∃ U ∈ nhds δ₀, ∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      AutomorphicForm.IsSemiLocalTestFn K L v φv → tsupport φv ⊆ U →
        ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ,
          AutomorphicForm.IsLocalTestFn K v fv ∧ AutomorphicForm.AreMatchingLocal K L v σ φv fv := by sorry
