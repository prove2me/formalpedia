-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_claim_3
-- name    : AnalystRank.Informativeness.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:00.70725+00:00
-- url     : https://prove2.me/theorems/e07f9691-4db5-4c83-8ef5-f740ad7b0d7e
-- title:
--   Claim 3 (B.2 corrected to φ > φ̄, C with σʰ ≥ 1 − σˡ) — comparison of g_l and g_h; the unique crossing σ̈ˡ ∈ (0, 1)
-- statement:
--   Let $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $w_1>w_0>w_2$ and $\varphi=(w_1-w_0)/(w_0-w_2)$. With $\Psi^h,\Psi^l$ the ratios (A.7), define
--
--   $$g_l(\sigma^h,\sigma^l)=\frac{\gamma}{1-\gamma}\Psi^l(\sigma^h,\sigma^l),\qquad g_h(\sigma^h,\sigma^l)=\frac{1-\gamma}{\gamma}\Psi^h(\sigma^h,\sigma^l).$$
--
--   1. **(A)** If $\rho=0$, then $g_l>g_h$ on all of $[0,1]^2$.
--   2. **(B.1)** If $\rho>0$, $\varphi>1$, and either $\rho\le\bar\rho$ or ($\rho>\bar\rho$ and $\varphi<\bar\varphi$), then $g_l(1,\sigma^l)>g_h(1,\sigma^l)$ for every $\sigma^l\in[0,1]$.
--   3. **(B.2)** If $\rho>0$, $\varphi>1$, $\rho>\bar\rho$ and $\varphi>\bar\varphi$, then there is a unique $\ddot\sigma^l\in(0,1)$ such that, for $\sigma^l\in[0,1]$, $g_l(1,\sigma^l)\ge g_h(1,\sigma^l)$ if $\sigma^l\le\ddot\sigma^l$ and $g_l(1,\sigma^l)<g_h(1,\sigma^l)$ if $\sigma^l>\ddot\sigma^l$. The quantity $\ddot\sigma^l$ of the closed-forms file is this point, and $g_l(1,\ddot\sigma^l)=g_h(1,\ddot\sigma^l)$, which is (B.6).
--   4. **(C)** If $\rho>0$ and $\varphi<1$, then $g_l(\sigma^h,\sigma^l)>g_h(\sigma^h,\sigma^l)$ for every $\sigma\in[0,1]^2$ with $\sigma^h\ge1-\sigma^l$.
--
--   The sign of $g_l-g_h$ decides, through (B.31), whether an analyst with a high signal still wants to forecast high once the low-signal type is indifferent.
--
--   **Formalization Note** Two corrections. *(B.2)* is stated for $\varphi>\bar\varphi$, not the printed $\varphi\ge\bar\varphi$: at $\varphi=\bar\varphi$, $g_l(1,\cdot)\ge g_h(1,\cdot)$ on all of $[0,1]$ with equality only at $\sigma^l=1$, so there is no crossing in $(0,1)$ (numerically, e.g. $\gamma=0.6$, $\rho=0.9$). *(C)* carries the paper's standing restriction $\sigma^h\ge1-\sigma^l$ (p. 9): without it the inequality fails, e.g. at $\gamma\approx0.609$, $\rho\approx0.977$, $\varphi\approx0.507$, $\sigma\approx(0.095,0.114)$.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), pp. 34–35, Claim 3 (A)–(C), (B.5a)–(B.6) (B.2 corrected to φ > φ̄; C restricted to σʰ ≥ 1 − σˡ)

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model
import Definitions.Def_AnalystRank_Informativeness_ClosedForms

namespace AnalystRank.Informativeness

open Set

theorem claim_3 (γ ρ w1 w0 w2 : ℝ) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hw1 : w0 < w1) (hw2 : w2 < w0) :
    (ρ = 0 → ∀ σ : ℝ × ℝ, σ.1 ∈ Icc (0 : ℝ) 1 → σ.2 ∈ Icc (0 : ℝ) 1 →
      gH w1 w0 w2 γ ρ σ < gL w1 w0 w2 γ ρ σ) ∧
    (0 < ρ → 1 < phi w1 w0 w2 → (ρ ≤ rhoBar γ ∨ (rhoBar γ < ρ ∧ phi w1 w0 w2 < phiBar γ ρ)) →
      ∀ y ∈ Icc (0 : ℝ) 1, gH w1 w0 w2 γ ρ (1, y) < gL w1 w0 w2 γ ρ (1, y)) ∧
    (0 < ρ → 1 < phi w1 w0 w2 → rhoBar γ < ρ → phiBar γ ρ < phi w1 w0 w2 →
      (∃! s : ℝ, s ∈ Ioo (0 : ℝ) 1 ∧ ∀ y ∈ Icc (0 : ℝ) 1,
        (y ≤ s → gH w1 w0 w2 γ ρ (1, y) ≤ gL w1 w0 w2 γ ρ (1, y)) ∧
        (s < y → gL w1 w0 w2 γ ρ (1, y) < gH w1 w0 w2 γ ρ (1, y))) ∧
      sigmaDDotL w1 w0 w2 γ ρ ∈ Ioo (0 : ℝ) 1 ∧
      (∀ y ∈ Icc (0 : ℝ) 1,
        (y ≤ sigmaDDotL w1 w0 w2 γ ρ → gH w1 w0 w2 γ ρ (1, y) ≤ gL w1 w0 w2 γ ρ (1, y)) ∧
        (sigmaDDotL w1 w0 w2 γ ρ < y → gL w1 w0 w2 γ ρ (1, y) < gH w1 w0 w2 γ ρ (1, y))) ∧
      gL w1 w0 w2 γ ρ (1, sigmaDDotL w1 w0 w2 γ ρ) = gH w1 w0 w2 γ ρ (1, sigmaDDotL w1 w0 w2 γ ρ)) ∧
    (0 < ρ → phi w1 w0 w2 < 1 → ∀ σ : ℝ × ℝ, σ.1 ∈ Icc (0 : ℝ) 1 → σ.2 ∈ Icc (0 : ℝ) 1 →
      1 - σ.2 ≤ σ.1 → gH w1 w0 w2 γ ρ σ < gL w1 w0 w2 γ ρ σ) := by sorry

end AnalystRank.Informativeness
