-- Prove2me | Theorems.Thm_BanditCovariates_ABSE_sum_qB
-- name    : BanditCovariates.ABSE.sum_qB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:11:50.357245+00:00
-- url     : https://prove2.me/theorems/191af26d-7483-43f8-abb0-60eb7abad71b
-- title:
--   §5, p. 25, display before (5.6) — Σ_{|B|=2^{-k}} q_B ≤ c₂ 2^{k(d−βα)}
-- statement:
--   Fix $d\ge1$, $0<\beta\le1$, $L>0$, $\alpha>0$, $0<\delta_0<1$, $C_0>0$ and $0<\underline c\le\bar c$. There is a constant $c_2>0$, depending only on these parameters, such that for every $K\ge2$, every machine of the class $\mathcal M^K_{\mathcal X}(\alpha,\beta,L)$ with margin constants $(\delta_0,C_0)$ and density bounds $(\underline c,\bar c)$, and every depth $k\ge0$,
--
--   $$\sum_{|B|=2^{-k}}q_B\le c_2\,2^{k(d-\beta\alpha)},$$
--
--   where the sum runs over the $2^{kd}$ cells of side $2^{-k}$ and $q_B=P_X(0<f^\star-f^\sharp\le c_1|B|^\beta\mid X\in B)$ with $c_1=2^{3+\beta}c_0$, $c_0=2Ld^{\beta/2}$.
--
--   This controls how many cells of a given depth contain a non-negligible amount of the region where the two best arms are close.
--
--   **Formalization Note** The page states the bound for $k\in\{0,\dots,k_0\}$; since $c_2$ does not depend on $n$ and $k_0\to\infty$ with $n$, this is the same as every $k$. The page's explicit value $c_2=c_1^\alpha/\underline c$ omits the margin constant $C_0$, so the existential form is stated.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 25, display before (5.6)

import Mathlib
import Definitions.Def_BanditCovariates_ABSE_ProofObjects

noncomputable section

namespace BanditCovariates.ABSE

/-- Display before (5.6), p. 25: the conditional margin masses of the cells of
depth k sum to at most `c₂ 2^{k(d-βα)}`, with `c₂` depending only on the class
parameters (not on K, the machine, or k). -/
theorem sum_qB (d : ℕ) (β L α δ₀ C₀ cLow cHigh : ℝ)
    (hd : 1 ≤ d) (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 < L) (hα : 0 < α)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ < 1) (hC₀ : 0 < C₀)
    (hcLow : 0 < cLow) (hcHigh : cLow ≤ cHigh) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (K : ℕ), 2 ≤ K →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (M : Machine d K Ω),
        InClass M β L α δ₀ C₀ cLow cHigh →
        ∀ k : ℕ, ∑ B ∈ cellsAt d k, qB M β L B ≤
          c₂ * (2 : ℝ) ^ ((k : ℝ) * ((d : ℝ) - β * α)) := by sorry

end BanditCovariates.ABSE
