-- Prove2me | Theorems.Thm_AutomorphicForm_relIndex_semiLocalIntegers_comap_sigmaTensor_sub_mulLeft_eq_absNorm_pow_min_of_subsingleton_extension
-- name    : AutomorphicForm.relIndex_semiLocalIntegers_comap_sigmaTensor_sub_mulLeft_eq_absNorm_pow_min_of_subsingleton_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/58fcd9ac-9790-509c-8251-6380fa3a4bda
-- title:
--   Lattice index at an inert unramified place of prime degree
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, assume the degree $[L:K] = \operatorname{finrank}_K L$ is a prime number, and let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$. Let $v$ be a height-one prime of $\mathcal{O}_K$, and write $q = \operatorname{absNorm}(v)$ for the absolute norm of its ideal. Assume every height-one prime $w$ of $\mathcal{O}_L$ lying under $v$ has $\mathrm{ramificationIdx}'$ equal to $1$, and that the type $v.\mathrm{Extension}\,(\mathcal{O}_L) = \{w : w \text{ lies over } v\}$ is a subsingleton. Let $c \in L \otimes_K K_v$, where $K_v$ is the $v$-adic completion of $K$, let $n \in K_v$ with $\|n\| = 1$, let $m \in \mathbb{N}$ with $\|1 - n\| = q^{-m}$, and assume that the product over $i \in \{0,\dots,[L:K]-1\}$ of the $i$-th iterates of $c$ under the ring endomorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K K_v$ equals $1 \otimes n$. Let $\varpi \in K_v$ with $\|\varpi\| = q^{-1}$, and let $s \in \mathbb{N}$. Write $R$ for the additive subgroup of $L \otimes_K K_v$ underlying the range of the algebra map $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_v \to L \otimes_K K_v$, and let $\Lambda$ be the intersection of the preimage of $R$ under the additive map $y \mapsto (\sigma \otimes \mathrm{id})(y) - cy$ with the preimage of $R$ under $y \mapsto (1 \otimes \varpi^s)\,y$. Then the index of $R \cap \Lambda$ in $\Lambda$ equals $q^{\min(s,m)}$.
--
--   This is the lattice count at a place of $K$ that is unramified and has a single prime above it in a Galois extension of prime degree: the semi-local algebra $L \otimes_K K_v$ is then the unramified degree $[L:K]$ extension $L_w$ of $K_v$, and the quotient $\Lambda/R$ is cyclic of order $q^{\min(s,m)}$. It supplies the arithmetic input to the evaluation of twisted weighted orbital integrals of indicator functions of semi-local integral sets at inert places, used by [`AutomorphicForm.eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_subsingleton_extension`](thm.html#AutomorphicForm.eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_subsingleton_extension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_relIndex_semiLocalIntegers_comap_sigmaTensor_sub_mulLeft_eq_absNorm_pow_min_of_subsingleton_extension.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.relIndex_semiLocalIntegers_comap_sigmaTensor_sub_mulLeft_eq_absNorm_pow_min_of_subsingleton_extension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hinert : Subsingleton (v.Extension (𝓞 L)))
    (c : L ⊗[K] v.adicCompletion K) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank K L),
        (⇑(AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ))^[i] c = (1 : L) ⊗ₜ[K] n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (s : ℕ) :
    (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.relIndex
        (((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
            ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).toAddMonoidHom -
              AddMonoidHom.mulLeft c)) ⊓
          ((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
            (AddMonoidHom.mulLeft ((1 : L) ⊗ₜ[K] (ϖ ^ s))))) =
      Ideal.absNorm v.asIdeal ^ min s m := by sorry
