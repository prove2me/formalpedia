-- Prove2me | Theorems.Thm_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
-- name    : Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/ee62d435-ca29-55dc-b654-2dde0c66727c
-- title:
--   De la Vallée Poussin–Landau zero-free region deduction
-- statement:
--   Let $F_1,F_2:\mathbb C\to\mathbb C$ be functions and let $\beta,\gamma,r,\mathcal L,C_0$ be real numbers with $0<r\le 1$, $r\mathcal L\ge 1$, and $0\le C_0\le\mathcal L$. Assume: $F_1(\beta+i\gamma)=0$; both $F_1$ and $F_2$ are non-vanishing on the open half-plane $\operatorname{Re}s>1$; for every real $\sigma$ with $1<\sigma\le 1+r$, $F_1$ is analytic on a neighbourhood of each point of the closed disc of radius $r$ centred at $\sigma+i\gamma$ and $F_2$ is analytic on a neighbourhood of each point of the closed disc of radius $r$ centred at $\sigma+2i\gamma$, with $\|F_1\|\le e^{\mathcal L}$ on the first disc and $\|F_2\|\le e^{\mathcal L}$ on the second; for every such $\sigma$ the lower bounds $|F_1(\sigma+i\gamma)|\ge(\sigma-1)^2e^{-\mathcal L}$ and $|F_2(\sigma+2i\gamma)|\ge(\sigma-1)^2e^{-\mathcal L}$ hold; and for every such $\sigma$ the $3$–$4$–$1$ inequality $$0\le 3\Big(\tfrac1{\sigma-1}+C_0\Big)+4\operatorname{Re}\Big({-\tfrac{F_1'}{F_1}(\sigma+i\gamma)}\Big)+\operatorname{Re}\Big({-\tfrac{F_2'}{F_2}(\sigma+2i\gamma)}\Big)$$ holds, the logarithmic derivatives being formed with Lean's `deriv`. The conclusion is the explicit gap $$\frac{r}{20000\,\mathcal L}\le 1-\beta .$$
--
--   This is the deduction step of the de la Vallée Poussin–Landau method for zero-free regions, isolated as a statement of pure complex analysis with explicit constants: growth $e^{\mathcal L}$ on discs, lower bounds $(\sigma-1)^2e^{-\mathcal L}$ at their centres, non-vanishing to the right of $\operatorname{Re}s=1$ and a $3$–$4$–$1$ inequality force any zero $\beta+i\gamma$ of $F_1$ to satisfy $1-\beta\ge r/(20000\mathcal L)$. It rests on a Borel–Carathéodory type bound for $-\operatorname{Re}(f'/f)$ in terms of the zeros in a half-sized disc, and is applied in the project to obtain zero-free regions for Hecke $L$-functions and Dedekind zeta functions of number fields, with $F_1$ and $F_2$ taken to be the relevant $L$-functions at $\chi$ and $\chi^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
    (F₁ F₂ : ℂ → ℂ) (β γ r 𝓛 C₀ : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (h𝓛 : 1 ≤ r * 𝓛) (hC₀ : 0 ≤ C₀) (hC₀𝓛 : C₀ ≤ 𝓛)
    (hρ : F₁ ((β : ℂ) + γ * Complex.I) = 0)
    (h1nz : ∀ s : ℂ, 1 < s.re → F₁ s ≠ 0)
    (h2nz : ∀ s : ℂ, 1 < s.re → F₂ s ≠ 0)
    (h1an : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      AnalyticOnNhd ℂ F₁ (Metric.closedBall ((σ : ℂ) + γ * Complex.I) r))
    (h2an : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      AnalyticOnNhd ℂ F₂ (Metric.closedBall ((σ : ℂ) + 2 * γ * Complex.I) r))
    (h1up : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      ∀ s ∈ Metric.closedBall ((σ : ℂ) + γ * Complex.I) r, ‖F₁ s‖ ≤ Real.exp 𝓛)
    (h2up : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      ∀ s ∈ Metric.closedBall ((σ : ℂ) + 2 * γ * Complex.I) r, ‖F₂ s‖ ≤ Real.exp 𝓛)
    (h1lo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖F₁ ((σ : ℂ) + γ * Complex.I)‖)
    (h2lo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖F₂ ((σ : ℂ) + 2 * γ * Complex.I)‖)
    (h341 : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      0 ≤ 3 * (1 / (σ - 1) + C₀)
        + 4 * (-(deriv F₁ ((σ : ℂ) + γ * Complex.I) / F₁ ((σ : ℂ) + γ * Complex.I))).re
        + (-(deriv F₂ ((σ : ℂ) + 2 * γ * Complex.I) / F₂ ((σ : ℂ) + 2 * γ * Complex.I))).re) :
    r / (20000 * 𝓛) ≤ 1 - β := by sorry
