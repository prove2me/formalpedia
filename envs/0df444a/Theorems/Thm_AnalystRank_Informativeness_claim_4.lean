-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_claim_4
-- name    : AnalystRank.Informativeness.claim_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:00.520321+00:00
-- url     : https://prove2.me/theorems/9989ce83-9a2e-4d7e-9ea4-957a7ba2dbb6
-- title:
--   Claim 4 — no fully mixed equilibrium if φ > 1, ρ = 0 or if φ < 1; for φ > 1, ρ > 0 an equilibrium (1, σˡ) dominates every fully mixed one
-- statement:
--   Let $q\in(0,1)$, $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$ and $w_1>w_0>w_2$, and consider the symmetric equilibria of the rank game at prior $q$.
--
--   1. **(A.1)** If $\varphi>1$ and $\rho=0$, there is no equilibrium with $\sigma^h\in(0,1)$ and $\sigma^l\in(0,1)$.
--   2. **(A.2)** If $\varphi>1$ and $\rho>0$, and both $(1,\sigma^l)$ with $\sigma^l\in(0,1)$ and some $\sigma'$ with $\sigma'^h,\sigma'^l\in(0,1)$ are equilibria, then $\sigma'^h\le1$ and $\sigma'^l\le\sigma^l$: the first is more informative in the sense of Definition 2.
--   3. **(B)** If $\varphi<1$, there is no equilibrium with $\sigma^h\in(0,1)$ and $\sigma^l\in(0,1)$.
--
--   This claim reduces the search for the most informative equilibrium to separating, semi-separating and pooling profiles.
--
--   **Formalization Note** "More informative" is read as Definition 2's coordinatewise order.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), p. 35, Claim 4

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model

namespace AnalystRank.Informativeness

open Set

theorem claim_4 (q γ ρ w1 w0 w2 : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hw1 : w0 < w1) (hw2 : w2 < w0) :
    (1 < phi w1 w0 w2 → ρ = 0 → ∀ σ ∈ rankEqSet w1 w0 w2 q γ ρ,
      ¬ (σ.1 ∈ Ioo (0 : ℝ) 1 ∧ σ.2 ∈ Ioo (0 : ℝ) 1)) ∧
    (1 < phi w1 w0 w2 → 0 < ρ → ∀ l ∈ Ioo (0 : ℝ) 1, ∀ σ' : ℝ × ℝ,
      ((1 : ℝ), l) ∈ rankEqSet w1 w0 w2 q γ ρ → σ' ∈ rankEqSet w1 w0 w2 q γ ρ →
      σ'.1 ∈ Ioo (0 : ℝ) 1 → σ'.2 ∈ Ioo (0 : ℝ) 1 → σ'.1 ≤ 1 ∧ σ'.2 ≤ l) ∧
    (phi w1 w0 w2 < 1 → ∀ σ ∈ rankEqSet w1 w0 w2 q γ ρ,
      ¬ (σ.1 ∈ Ioo (0 : ℝ) 1 ∧ σ.2 ∈ Ioo (0 : ℝ) 1)) := by sorry

end AnalystRank.Informativeness
