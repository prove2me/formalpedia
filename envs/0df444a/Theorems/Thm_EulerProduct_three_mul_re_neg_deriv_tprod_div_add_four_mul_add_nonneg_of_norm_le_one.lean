-- Prove2me | Theorems.Thm_EulerProduct_three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one
-- name    : EulerProduct.three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/b9e9b15e-b267-58df-aa15-cc8b52906681
-- title:
--   The 3–4–1 inequality for Euler products
-- statement:
--   Let $\iota$ be a type, and let $N : \iota \to \mathbb{N}$ satisfy $N_i \ge 2$ for every $i$. Let $c, c_2 : \iota \to \mathbb{C}$ be families with $\|c_i\| \le 1$ and $\|c_{2,i}\| \le 1$ for all $i$, and suppose that for each $i$ either $c_i = 0$ or $c_{2,i} = c_i^2$. Assume that for every real $\sigma > 1$ the family $i \mapsto (N_i)^{-\sigma}$ is summable. Fix real numbers $\sigma, t$ with $1 < \sigma$. Write, for a family of coefficients $b$, $E_b(z) = \prod_i' (1 - b_i N_i^{-z})^{-1}$ for the unconditional infinite product over $\iota$ (Mathlib's `tprod`, equal to $1$ when the family is not multipliable), and let $E_1(z) = \prod_i' (1 - N_i^{-z})^{-1}$ be the product with all coefficients equal to $1$, written without coefficient. Then
--   $$3\,\operatorname{Re}\Bigl(-\frac{E_1'(\sigma)}{E_1(\sigma)}\Bigr) + 4\,\operatorname{Re}\Bigl(-\frac{E_c'(\sigma + it)}{E_c(\sigma + it)}\Bigr) + \operatorname{Re}\Bigl(-\frac{E_{c_2}'(\sigma + 2it)}{E_{c_2}(\sigma + 2it)}\Bigr) \;\ge\; 0,$$
--   where each derivative is the complex derivative of the corresponding product as a function of $z$, taken at the indicated point, and each quotient is a quotient of complex numbers (so the assertion is about the real part of the three-term combination in the form displayed).
--
--   This is the logarithmic-derivative form of the Mertens–de la Vallée Poussin device $3 + 4\cos\theta + \cos 2\theta = 2(1+\cos\theta)^2 \ge 0$, applied to a general Euler product with coefficients of modulus at most $1$ satisfying $c_{2,i} = c_i^2$ away from the vanishing indices. It is used in the construction of zero-free regions of the shape $\operatorname{Re} z > 1 - c/\log(\cdots)$: it feeds the non-vanishing statements [`NumberField.TateGlobal.exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus`](thm.html#NumberField.TateGlobal.exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus) and [`NumberField.TateGlobal.exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re`](thm.html#NumberField.TateGlobal.exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EulerProduct_three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem EulerProduct.three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one
    {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i)
    (c c₂ : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1) (hc₂ : ∀ i, ‖c₂ i‖ ≤ 1)
    (hcc : ∀ i, c i = 0 ∨ c₂ i = c i ^ 2)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ))
    (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-(deriv (fun z : ℂ => ∏' i, (1 - ((N i : ℕ) : ℂ) ^ (-z))⁻¹) (σ : ℂ) /
              ∏' i, (1 - ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)).re
      + 4 * (-(deriv (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹)
                ((σ : ℂ) + t * Complex.I) /
              ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I)))⁻¹)).re
      + (-(deriv (fun z : ℂ => ∏' i, (1 - c₂ i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹)
                ((σ : ℂ) + 2 * t * Complex.I) /
              ∏' i, (1 - c₂ i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * t * Complex.I)))⁻¹)).re := by sorry
