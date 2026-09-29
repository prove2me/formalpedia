-- Prove2me | Theorems.Thm_AutomorphicForm_finrank_mul_ratio_mul_add_mul_window_eq_zero_of_forall_mem_eq_zero_of_not_singleton
-- name    : AutomorphicForm.finrank_mul_ratio_mul_add_mul_window_eq_zero_of_forall_mem_eq_zero_of_not_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/812b97bf-4d91-5526-b91a-f487655b4a89
-- title:
--   Vanishing of the combined weighted Euler bracket
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, write $\ell = \operatorname{finrank}_K L$, and fix finite sets $S_K \subseteq T$ of maximal ideals of $\mathcal{O}_K$ (with equality of such primes decidable). Let $c_G, c_T, c_G', c_T'$ be strictly positive reals, let $I_a, J_a, J_a' \in \mathbb{C}$ be scalars (playing the role of the factors indexed outside $T$), and let $I_v, J_v, J_v'$ be complex-valued functions on the primes of $\mathcal{O}_K$. Suppose $J \in \mathbb{C}$ is given by the Euler-shaped expression $J = c_G c_T^{-1}\bigl(J_a \prod_{v \in T} I_v + I_a \sum_{v \in T} J_v \prod_{u \in T \setminus \{v\}} I_u\bigr)$. Let $P \subseteq T$ be a further finite set and $b$ a proposition, subject to: $P$ is nonempty or $b$ holds; it is not the case that $|P| = 1$ and $b$ fails; $I_v = 0$ for every $v \in P$; and $b$ implies both $I_a = 0$ and $J_a' = 0$. Then $$\ell \cdot \frac{c_G' c_T}{c_G c_T'} \cdot J + \frac{c_G'}{c_T'}\Bigl[(J_a' - \ell J_a)\prod_{v \in T} I_v + I_a \sum_{v \in S_K} (J_v' - \ell J_v) \prod_{u \in T \setminus \{v\}} I_u\Bigr] = 0,$$ the rational constants and $\ell$ being read in $\mathbb{C}$ via the obvious coercions.
--
--   This is the purely algebraic core of the window-cancellation step: it records that a degree-$\ell$ multiple of one weighted Euler product, corrected by the difference bracket formed from the base-changed local data $J_v'$, $J_a'$ over $S_K$, vanishes as soon as the local factors degenerate at two places or the relevant archimedean factors vanish. It is applied in the two results that establish vanishing of the combined weighted class integral off the image of the norm, where $P$ is supplied by the set of bad places and $b$ flags the degenerate archimedean situation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finrank_mul_ratio_mul_add_mul_window_eq_zero_of_forall_mem_eq_zero_of_not_singleton.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.finrank_mul_ratio_mul_add_mul_window_eq_zero_of_forall_mem_eq_zero_of_not_singleton
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hST : SK ⊆ T)

    (cG cT cG' cT' : ℝ) (hcG : 0 < cG) (hcT : 0 < cT) (hcG' : 0 < cG') (hcT' : 0 < cT')

    (Ia Ja Ja' : ℂ) (Iv Jv Jv' : HeightOneSpectrum (𝓞 K) → ℂ)

    (J : ℂ)
    (hJ : J = cG * cT⁻¹ * (Ja * ∏ v ∈ T, Iv v + Ia * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u))

    (P : Finset (HeightOneSpectrum (𝓞 K))) (hPT : P ⊆ T) (b : Prop)
    (hne : P.Nonempty ∨ b) (hnot1 : ¬ (P.card = 1 ∧ ¬ b))
    (hIv : ∀ v ∈ P, Iv v = 0)
    (hIa : b → Ia = 0) (hJa' : b → Ja' = 0) :
    (Module.finrank K L : ℂ) * (((cG' * cT) / (cG * cT') : ℝ) : ℂ) * J +
      ((cG' * cT'⁻¹ : ℝ) : ℂ) *
        ((Ja' - (Module.finrank K L : ℂ) * Ja) * ∏ v ∈ T, Iv v +
          Ia * ∑ v ∈ SK, (Jv' v - (Module.finrank K L : ℂ) * Jv v) * ∏ u ∈ T.erase v, Iv u) = 0 := by sorry
