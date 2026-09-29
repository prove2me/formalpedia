-- Prove2me | Theorems.Thm_AutomorphicForm_exists_idempotent_orbit_or_isField_tensor_adicCompletion
-- name    : AutomorphicForm.exists_idempotent_orbit_or_isField_tensor_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/ea90d1d4-0373-59f1-af6f-5188862fcddb
-- title:
--   Split-or-inert dichotomy for L⊗_K Kᵥ in prime degree
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, assume the degree $n = [L:K]$, i.e. `Module.finrank K L`, is a prime number, let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$, and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, with associated completion $K_v =$ `v.adicCompletion K`. Write $\sigma \otimes 1$ for the ring endomorphism `sigmaTensor K L (v.adicCompletion K) σ` of $L \otimes_K K_v$, namely the map obtained by tensoring $\sigma$ with the identity of $K_v$. The conclusion is a disjunction: either there exists an element $e \in L \otimes_K K_v$ with $e^2 = e$, such that $e \cdot (\sigma \otimes 1)^i(e) = 0$ for every $i$ with $0 < i < n$, where $(\sigma \otimes 1)^i$ denotes the $i$-fold iterate of the underlying map, and such that $\sum_{i=0}^{n-1} (\sigma \otimes 1)^i(e) = 1$; or else $L \otimes_K K_v$ is a field in the sense of Mathlib's `IsField`. The two alternatives are not asserted to be mutually exclusive.
--
--   This is the split/inert dichotomy for the base change of a prime-degree extension to a completion: since $n$ is prime and $\sigma \neq 1$, the extension is cyclic with $\sigma$ a generator, and a finite place of $K$ either splits completely in $L$ — giving, via $L \otimes_K K_v \cong \prod_{w \mid v} L_w$, a $\sigma$-orbit of orthogonal idempotents summing to $1$ — or has a unique place $w$ above it, so that $L \otimes_K K_v = L_w$ is a field. It serves the construction of regular semisimple elements and of norms in the twisted orbital part of the development, being used by [`AutomorphicForm.exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one`](thm.html#AutomorphicForm.exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one) and by [`AutomorphicForm.exists_mem_twistedCentralizer_isRegularSemisimple_not_isSquare_isNormOf_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_mem_twistedCentralizer_isRegularSemisimple_not_isSquare_isNormOf_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_idempotent_orbit_or_isField_tensor_adicCompletion.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.exists_idempotent_orbit_or_isField_tensor_adicCompletion
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) :
    (∃ e : L ⊗[K] v.adicCompletion K, IsIdempotentElem e ∧
        (∀ i, 0 < i → i < Module.finrank K L →
          e * (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[i] e = 0) ∧
        (∑ i ∈ Finset.range (Module.finrank K L),
          (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[i] e) = 1) ∨
      IsField (L ⊗[K] v.adicCompletion K) := by sorry
