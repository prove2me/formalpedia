-- Prove2me | Theorems.Thm_EisensteinGeneral_LocalCorrection_exists_forall_norm_corrOn_le_of_le_re
-- name    : EisensteinGeneral.LocalCorrection.exists_forall_norm_corrOn_le_of_le_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/7a05ab79-162a-5fb6-94a0-beec590ffb43
-- title:
--   Uniform half-plane bound for the local correction factor
-- statement:
--   Let $N$ be a natural number with $N\ge 2$, let $n\in\mathbb Z$, let $c_0,m_0\in\mathbb N$, let $\mu_{\mathcal O}$ be a real number with $\mu_{\mathcal O}>0$, and let $c_0',b,d,\sigma_1$ be real numbers with $c_0'\ge 0$, $b\ge 0$ and $d\ge 1$. Then there exist a real number $E\ge 0$ and a natural number $\kappa$, depending only on these data, such that for all $c,m\in\mathbb N$, all $e\in\mathbb Z$, all $\gamma_0\in\mathbb C$, every sequence $\mathrm{sh}:\mathbb N\to\mathbb C$ and every $s\in\mathbb C$ satisfying $c\le c_0$, $m\le m_0$, $\lVert\gamma_0\rVert\le c_0'$, $\lVert\mathrm{sh}(k)\rVert\le b\,d^{k}$ for all $k\ge 1$, and $\sigma_1\le\operatorname{Re} s$, one has $\lVert \mathrm{corrOn}\,N\,n\,c\,m\,e\,\mu_{\mathcal O}\,\gamma_0\,\mathrm{sh}\,s\rVert\le E\cdot\bigl(N^{\max(0,-e)}\bigr)^{\kappa}$. Here `corrOn` is $0$ unless $e\le n+\max(m,c)$, and in that case equals $\mu_{\mathcal O}^{-1}\bigl(\gamma_0+\sum_{k=1}^{K}\bigl(N^{-(2s+1)}\bigr)^{k}\,\mathrm{sh}(k)\bigr)$ with $K=\max\bigl(0,\max(m-1,\,n+c-e)\bigr)$, the truncation length being taken as a natural number.
--
--   This is the uniform strip estimate for the ramified local correction factor occurring in the Whittaker coefficients of Bruhat-cell Eisenstein series: the constants $E$ and $\kappa$ are independent of the depth $c\le c_0$, the level $m\le m_0$, the frequency exponent $e$, the constant term, the shell coefficients and the point $s$ in the half-plane $\operatorname{Re} s\ge\sigma_1$. It feeds the uniform bound for Whittaker coefficients of Eisenstein series on balls, where the polynomial growth in $N^{\max(0,-e)}$ is what is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_LocalCorrection_exists_forall_norm_corrOn_le_of_le_re.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_EisensteinGeneral_LocalCorrection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open EisensteinGeneral.LocalCorrection

theorem EisensteinGeneral.LocalCorrection.exists_forall_norm_corrOn_le_of_le_re
    {N : ℕ} (hN : 2 ≤ N) (n : ℤ) (c₀ m₀ : ℕ) {μ𝒪 : ℝ} (hμ : 0 < μ𝒪)
    (c₀' b d σ₁ : ℝ) (hc₀' : 0 ≤ c₀') (hb : 0 ≤ b) (hd : 1 ≤ d) :
    ∃ E : ℝ, ∃ κ : ℕ, 0 ≤ E ∧ ∀ (c m : ℕ) (e : ℤ) (γ₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ),
      c ≤ c₀ → m ≤ m₀ → ‖γ₀‖ ≤ c₀' → (∀ k, 1 ≤ k → ‖sh k‖ ≤ b * d ^ k) → σ₁ ≤ s.re →
        ‖corrOn N n c m e μ𝒪 γ₀ sh s‖ ≤ E * ((N : ℝ) ^ (-e).toNat) ^ κ := by sorry
