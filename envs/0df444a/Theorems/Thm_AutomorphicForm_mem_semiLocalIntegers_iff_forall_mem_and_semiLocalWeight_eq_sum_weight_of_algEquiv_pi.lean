-- Prove2me | Theorems.Thm_AutomorphicForm_mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi
-- name    : AutomorphicForm.mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/0f0fc05e-464b-5ee1-914e-719e0a27c081
-- title:
--   Any Kᵥ-splitting computes semi-local integers and weights
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of $\mathcal O_K$ (a point of the height one spectrum), write $K_v$ for `v.adicCompletion K` and $\mathcal O_v$ for `v.adicCompletionIntegers K`, let $\iota$ be a finite index type, and let $e \colon L \otimes_K K_v \to (\iota \to K_v)$ be an isomorphism of $K_v$-algebras onto the product of $\iota$ copies of $K_v$. Then two assertions hold simultaneously. First, an element $x \in L \otimes_K K_v$ lies in [`AutomorphicForm.semiLocalIntegers K L v`](def/AutomorphicForm_TwistedOrbital.html#L98), that is, in the image of the canonical $\mathcal O_L$-algebra map $\mathcal O_L \otimes_{\mathcal O_K} \mathcal O_v \to L \otimes_K K_v$, if and only if for every $i \in \iota$ the coordinate $e(x)_i$ lies in $\mathcal O_v$. Second, for every $g \in \mathrm{GL}_2(L \otimes_K K_v)$ the semi-local weight of $g$ — by definition the (finite-support) sum, over the primes $w$ of $\mathcal O_L$ lying under $v$, of $2\log\bigl(\max(\lVert a_{00}\rVert,\lVert a_{01}\rVert)\cdot\max(\lVert a_{10}\rVert,\lVert a_{11}\rVert)/\lVert\det a\rVert\bigr)$ evaluated on the image $a$ of $g$ in $\mathrm{GL}_2(L_w)$ under the base-change identification of $L \otimes_K K_v$ with $\prod_{w \mid v} L_w$ — equals $\sum_{i \in \iota}$ of the same weight expression applied to the image of $g$ in $\mathrm{GL}_2(K_v)$ under the map functorially induced by the ring homomorphism underlying $e$ followed by the $i$-th coordinate projection.
--
--   This is the dictionary saying that the integral subring and the $\mathrm{GL}_2$ weight attached to the semi-local algebra $L \otimes_K K_v$ may be read off in an arbitrary $K_v$-algebra splitting of that algebra into copies of $K_v$, rather than only in the canonical splitting into the completions $L_w$ for $w \mid v$. It is used in the evaluation of twisted weighted orbital integrals of the indicator function of the semi-local integral set at a place of $K$ splitting completely in $L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι]
    (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (ι → v.adicCompletion K)) :
    (∀ x : L ⊗[K] v.adicCompletion K,
        x ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ i : ι, e x i ∈ v.adicCompletionIntegers K) ∧
    (∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.semiLocalWeight K L v g =
          ∑ i : ι, AutomorphicForm.LocalWeight.weight
            (Matrix.GeneralLinearGroup.map
              ((Pi.evalAlgHom (v.adicCompletion K) (fun _ : ι => v.adicCompletion K) i).comp
                e.toAlgHom).toRingHom g)) := by sorry
