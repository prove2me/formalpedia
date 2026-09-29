-- Prove2me | Theorems.Thm_AutomorphicForm_SplitPlace_exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq
-- name    : AutomorphicForm.SplitPlace.exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/172bac89-efcd-5a24-873d-2bde97db273d
-- title:
--   Split-place coordinates agree with the completions L_w
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra whose degree $n = \operatorname{finrank}_K L$ is prime, let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$, let $v$ be a height-one prime of $\mathcal{O}_K$, and let $\iota : L \to K_v$ be a $K$-algebra homomorphism into the $v$-adic completion of $K$. The assertion is that there exist a bijection $e$ from $\mathrm{Fin}\,n$ onto the set of height-one primes $w$ of $\mathcal{O}_L$ with $w \cap \mathcal{O}_K = v$, and, for each $i$, a $K_v$-algebra isomorphism $\theta_i : L_{e(i)} \to K_v$ from the $e(i)$-adic completion of $L$, such that three compatibilities hold. First, for every $z \in L \otimes_K K_v$ and every $i$, the $i$-th component of [`AutomorphicForm.SplitPlace.psi`](def/AutomorphicForm_SplitFibreIntegral.html#L77), i.e. of the $K$-algebra map $L \otimes_K K_v \to (K_v)^n$ sending $l \otimes a$ to $(\iota(\sigma^i(l))\,a)_i$, equals $\theta_i$ applied to the $e(i)$-component of the image of $z$ under the canonical isomorphism $L \otimes_K K_v \cong \prod_{w \mid v} L_w$ of `HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv`. Second, $\theta_i$ matches valuation rings: $\theta_i(y)$ lies in the ring of integers of $K_v$ if and only if $y$ lies in that of $L_{e(i)}$. Third, $\|\theta_i(y)\| = \|y\|$ for all $y \in L_{e(i)}$.
--
--   This is the split-place dictionary: a $K$-embedding of $L$ into $K_v$ forces $v$ to split completely in $L$, and under the classical decomposition $L \otimes_K K_v \cong \prod_{w \mid v} L_w$ the abstract coordinates $\psi_i$, built from $\iota$ and the powers of $\sigma$, are the completions $L_w$, factor by factor, compatibly with valuation rings and normalised absolute values. It is used to transport integrality, weight and Haar-measure statements between the two descriptions, as in [`AutomorphicForm.SplitPlace.mem_semiLocalIntegralSet_iff_coords_and_semiLocalWeight_eq_sum_and_map_coords_semiLocalHaar`](thm.html#AutomorphicForm.SplitPlace.mem_semiLocalIntegralSet_iff_coords_and_semiLocalWeight_eq_sum_and_map_coords_semiLocalHaar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SplitPlace_exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.SplitPlace.exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (ι : L →ₐ[K] v.adicCompletion K) :
    ∃ (e : Fin (Module.finrank K L) ≃ v.Extension (𝓞 L))
      (θ : ∀ i : Fin (Module.finrank K L), ((e i).1.adicCompletion L) ≃ₐ[v.adicCompletion K] v.adicCompletion K),
      (∀ (z : L ⊗[K] v.adicCompletion K) (i : Fin (Module.finrank K L)),
        AutomorphicForm.SplitPlace.psi K L (v.adicCompletion K) σ ι z i =
          θ i (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v z (e i))) ∧
      (∀ (i : Fin (Module.finrank K L)) (y : (e i).1.adicCompletion L),
        θ i y ∈ v.adicCompletionIntegers K ↔ y ∈ (e i).1.adicCompletionIntegers L) ∧
      (∀ (i : Fin (Module.finrank K L)) (y : (e i).1.adicCompletion L), ‖θ i y‖ = ‖y‖) := by sorry
