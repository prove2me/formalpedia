-- Prove2me | Theorems.Thm_AutomorphicForm_SatakeCombination_mul_sum_slotCoeff_div_pow_mul_ite_apply_T_add_T_inv_pow_eq_ite_sqrt_mul_pow_mul_zpow_neg
-- name    : AutomorphicForm.SatakeCombination.mul_sum_slotCoeff_div_pow_mul_ite_apply_T_add_T_inv_pow_eq_ite_sqrt_mul_pow_mul_zpow_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/f6a581c4-3a22-5ccb-b1b4-a01a0a175a9b
-- title:
--   Satake slot combination equals tilted Laurent symbol coefficient
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let `ws` assign to every height-one prime $v$ of $\mathcal{O}_K$ an element of `v.Extension (𝓞 L)`, that is, a height-one prime $w$ of $\mathcal{O}_L$ lying under which one finds $v$. Fix such a $v$ and natural numbers $k, j$. Write $f =$ `slotDeg K L ws v`, the inertia degree `v.asIdeal.inertiaDeg' (ws v).1.asIdeal`, and assume $0 < f$. Let $N_w$ be a natural number with $N_w =$ `Ideal.absNorm (ws v).1.asIdeal` and $N_w = (\mathrm{absNorm}\, v)^{f}$. Let $\zeta, s, x \in \mathbb{C}$ with $\zeta \neq 0$, $s^2 = \zeta$ and $x^{f} = \zeta$, and let $m_1, m_2 \in \mathbb{Z}$. Here `slotWord K L ws v k j` is the polynomial `satakePow f (X 0) (X 1) ^ k * ((X 1) ^ f) ^ j` in $\mathbb{C}[X_0, X_1]$, and `slotCoeff K L ws v k j r` is its coefficient at the exponent $r$ multiplied by $(\mathrm{absNorm}\, v)^{r(1)}$ and divided by $N_w^{\,j}$. The assertion is the identity $$(x\,\mathrm{absNorm}\,v)^{m_2} \sum_{r} \frac{\mathrm{slotCoeff}(r)}{(\mathrm{absNorm}\,v)^{r(1)}}\,\mathbf 1\!\left[m_1 + m_2 = r(0) + 2r(1)\right] \left[(T + T^{-1})^{r(0)}\right]_{m_1 - m_2} = \mathbf 1\!\left[f \mid m_2 \ \text{and}\ m_1 + m_2 = f(k + 2j)\right] (\sqrt{N_w}\,s)^{k}\,\zeta^{j}\,\left[(T + T^{-1})^{k}\right]_{n}\,(\sqrt{N_w}\,s)^{-n},$$ where $r$ ranges over the support of `slotWord K L ws v k j`, the brackets denote coefficients of Laurent polynomials over $\mathbb{C}$ in the variable $T$, $n = (m_1 - m_2)/f$ is the integer quotient, and the last factor is an integer power.
--
--   This is the per-place matching identity for the Satake data of a base-changed Hecke word: the combination of local coefficients attached to $v$ on the shell $(m_1, m_2)$ is concentrated on the congruence conditions $f \mid m_2$ and $m_1 + m_2 = f(k + 2j)$, where it reduces to the corresponding Laurent (Chebyshev) symbol coefficient at $n = (m_1-m_2)/f$ multiplied by the explicit tilt $(\sqrt{N_w}\,s)^{-n}$. It is used by [`AutomorphicForm.sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow`](thm.html#AutomorphicForm.sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow), where the tilt is absorbed into the winding datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SatakeCombination_mul_sum_slotCoeff_div_pow_mul_ite_apply_T_add_T_inv_pow_eq_ite_sqrt_mul_pow_mul_zpow_neg.lean

import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AutomorphicForm.SatakeCombination.mul_sum_slotCoeff_div_pow_mul_ite_apply_T_add_T_inv_pow_eq_ite_sqrt_mul_pow_mul_zpow_neg
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (k j : ℕ)

    (hf : 0 < AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (Nw : ℕ) (hNw : Ideal.absNorm (ws v).1.asIdeal = Nw)
    (hNwf : Nw = Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v)

    (ζ s x : ℂ) (hζ : ζ ≠ 0) (hs : s ^ 2 = ζ)
    (hx : x ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v = ζ)
    (m₁ m₂ : ℤ) :
    (x * (Ideal.absNorm v.asIdeal : ℂ)) ^ m₂ *
        ∑ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support,
          AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j r /
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) *
            (if m₁ + m₂ = ((r 0 : ℕ) : ℤ) + 2 * ((r 1 : ℕ) : ℤ) then
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ (r 0) : LaurentPolynomial ℂ).coeff (m₁ - m₂)
            else 0) =
      if (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ∣ m₂ ∧
          m₁ + m₂ = (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) * ((k : ℤ) + 2 * (j : ℤ)) then
        ((Real.sqrt (Nw : ℝ) : ℂ) * s) ^ k * ζ ^ j *
            ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff
              ((m₁ - m₂) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)) *
          ((Real.sqrt (Nw : ℝ) : ℂ) * s) ^ (-((m₁ - m₂) / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)))
      else 0 := by sorry
