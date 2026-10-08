-- Prove2me | Theorems.Thm_ErschlerZheng_exists_measure_mass_le_rpow_and_exp_le_growth
-- name    : ErschlerZheng.exists_measure_mass_le_rpow_and_exp_le_growth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T10:41:27.173535+00:00
-- url     : https://prove2.me/theorems/95af56a7-b4e9-45c8-8eae-62f506f0fb5e
-- title:
--   Theorem A — on the first Grigorchuk group, for ε > 0 a non-degenerate symmetric finite-entropy μ with non-trivial boundary and μ{|g| ⩾ r} ⩽ C_ε r^{−α_0+ε}; so v(n) ⩾ exp(c_ε n^{α_0−ε})
-- statement:
--   Let $G = G_{\mathbf{012}}$ be the first Grigorchuk group (`grigorchuk firstString`), with generating set $S = \{a, b, c, d\}$ (`genSet firstString`), and let $\alpha_0 = \frac{\log 2}{\log\lambda_0}$ (`alpha0`). Then:
--
--   1. for every $\epsilon > 0$ there are $C > 0$ and a non-degenerate (`IsNondegenerate`), symmetric (`IsSymmetric`) probability $\mu$ on $G$ (`IsProbability`) of finite entropy (`HasFiniteEntropy`) with non-trivial Poisson boundary (`HasNontrivialPoissonBoundary`) such that $\mu(\{g : l_S(g) \ge r\}) \le Cr^{-\alpha_0+\epsilon}$ for every real $r \ge 1$ (`mass`, `wordLength`);
--   2. for every $\epsilon > 0$ there is $c > 0$ with $v_{G,S}(n) \ge \exp(cn^{\alpha_0-\epsilon})$ for every $n \ge 1$ (`growth`).
--
--   Erschler and Zheng, p. 2, Theorem A: “Let $\alpha_0 = \frac{\log 2}{\log\lambda_0} \approx 0.7674$, where $\lambda_0$ is the positive root of the polynomial $X^3 - X^2 - 2X - 4$. For any $\epsilon > 0$, there exists a constant $C_\epsilon > 0$ and a non-degenerate symmetric probability measure $\mu$ on $G = G_{012}$ of finite entropy and nontrivial Poisson boundary, where the tail decay of $\mu$ satisfies that for all $r \geqslant 1$, $\mu(\{g : l_S(g) \geqslant r\}) \leqslant C_\epsilon r^{-\alpha_0+\epsilon}$. As a consequence, for any $\epsilon > 0$, there exists a constant $c_\epsilon > 0$ such that for all $n \geqslant 1$, $v_{G,S}(n) \geqslant \exp(c_\epsilon n^{\alpha_0-\epsilon})$.”
--
--   $\lambda_0$ and $\alpha_0$ are those of the Grigorchuk bundle; that $\lambda_0$ is the unique positive root and $\alpha_0 \approx 0.7674$ is the milestone [`ErschlerZheng.existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM`](https://prove2.me/theorems/fdf7cb37-4cf2-43d0-b0d2-f089f2d15823). The paper introduces Theorem A as “Our main result Theorem 8.3 specialized to the first Grigorchuk group $G_{012}$” (p. 2).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 2, Theorem A

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem exists_measure_mass_le_rpow_and_exp_le_growth :
    (∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∃ μ : grigorchuk firstString → ℝ,
      IsNondegenerate μ ∧ IsSymmetric μ ∧ IsProbability μ ∧ HasFiniteEntropy μ ∧
        HasNontrivialPoissonBoundary μ ∧
        ∀ r : ℝ, 1 ≤ r →
          mass μ {g | r ≤ (wordLength (genSet firstString) g : ℝ)} ≤ C * r ^ (-alpha0 + ε)) ∧
    ∀ ε > (0 : ℝ), ∃ c > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      Real.exp (c * (n : ℝ) ^ (alpha0 - ε)) ≤ growth (genSet firstString) n := by
  sorry

end ErschlerZheng
