-- Prove2me | Theorems.Thm_AutomorphicForm_sub_finrank_mul_ratio_mul_eq_mul_window_arch_add_sum_window_of_forall_eq_of_forall_eq_finrank_mul
-- name    : AutomorphicForm.sub_finrank_mul_ratio_mul_eq_mul_window_arch_add_sum_window_of_forall_eq_of_forall_eq_finrank_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/565418f3-0897-5c69-a697-69843c4f62aa
-- title:
--   Cancellation of the weighted terms outside S_K
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $\ell$ denote the image of $[L:K] =$ `Module.finrank K L` in $\mathbb{C}$. Let $S_K \subseteq T$ be finite sets of nonzero primes of $\mathcal{O}_K$ (with decidable equality on the height-one spectrum), let $c_G, c_T, c_G', c_T'$ be strictly positive reals, let $I_\infty', J_\infty', I_\infty, J_\infty \in \mathbb{C}$ (written `Ia'`, `Ja'`, `Ia`, `Ja`), and let $I_v', J_v', I_v, J_v$ be complex-valued functions on the primes. Assume the two quantities $J'$ and $J$ are given by the Euler-factorised expressions $J' = c_G' c_T'^{-1}\bigl(J_\infty' \prod_{v \in T} I_v' + I_\infty' \sum_{v \in T} J_v' \prod_{u \in T \setminus \{v\}} I_u'\bigr)$ and $J = c_G c_T^{-1}\bigl(J_\infty \prod_{v \in T} I_v + I_\infty \sum_{v \in T} J_v \prod_{u \in T \setminus \{v\}} I_u\bigr)$, and assume the matching conditions $I_\infty' = I_\infty$, $I_v' = I_v$ for all $v \in T$, and $J_v' = \ell\, J_v$ for all $v \in T$ with $v \notin S_K$. Then $$J' - \ell \cdot \frac{c_G' c_T}{c_G c_T'} \cdot J = c_G' c_T'^{-1}\Bigl((J_\infty' - \ell J_\infty)\prod_{v \in T} I_v + I_\infty \sum_{v \in S_K} (J_v' - \ell J_v)\prod_{u \in T \setminus \{v\}} I_u\Bigr),$$ the real scalars being coerced to $\mathbb{C}$.
--
--   This is the per-class bookkeeping step in the comparison of the weighted (hyperbolic) terms of two trace formulas for cyclic base change on $\mathrm{GL}_2$: once the local weighted values away from $S_K$ differ exactly by the factor $[L:K]$, all such places drop out of the difference, leaving only an archimedean window term and finitely many window terms indexed by $S_K$. It is used by [`AutomorphicForm.twistedWeightedClassIntegral_eq_finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_of_coupled_of_isSemiLocalFactorization`](thm.html#AutomorphicForm.twistedWeightedClassIntegral_eq_finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_of_coupled_of_isSemiLocalFactorization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sub_finrank_mul_ratio_mul_eq_mul_window_arch_add_sum_window_of_forall_eq_of_forall_eq_finrank_mul.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.sub_finrank_mul_ratio_mul_eq_mul_window_arch_add_sum_window_of_forall_eq_of_forall_eq_finrank_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hST : SK ⊆ T)

    (cG cT cG' cT' : ℝ) (hcG : 0 < cG) (hcT : 0 < cT) (hcG' : 0 < cG') (hcT' : 0 < cT')

    (Ia' Ja' Ia Ja : ℂ) (Iv' Jv' Iv Jv : HeightOneSpectrum (𝓞 K) → ℂ)

    (J' J : ℂ)
    (hJ' : J' = cG' * cT'⁻¹ * (Ja' * ∏ v ∈ T, Iv' v + Ia' * ∑ v ∈ T, Jv' v * ∏ u ∈ T.erase v, Iv' u))
    (hJ : J = cG * cT⁻¹ * (Ja * ∏ v ∈ T, Iv v + Ia * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u))

    (hIa : Ia' = Ia) (hIv : ∀ v ∈ T, Iv' v = Iv v)
    (hJv : ∀ v ∈ T, v ∉ SK → Jv' v = (Module.finrank K L : ℂ) * Jv v) :
    J' - (Module.finrank K L : ℂ) * (((cG' * cT) / (cG * cT') : ℝ) : ℂ) * J =
      ((cG' * cT'⁻¹ : ℝ) : ℂ) *
        ((Ja' - (Module.finrank K L : ℂ) * Ja) * ∏ v ∈ T, Iv v +
          Ia * ∑ v ∈ SK, (Jv' v - (Module.finrank K L : ℂ) * Jv v) * ∏ u ∈ T.erase v, Iv u) := by sorry
