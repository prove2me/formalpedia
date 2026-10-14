-- Prove2me | Theorems.Thm_DirectedOpinion_Memory_theorem_8
-- name    : DirectedOpinion.Memory.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:02.886381+00:00
-- url     : https://prove2.me/theorems/2191c33a-a73f-4bd4-9c70-bdcf6705e4f3
-- title:
--   Theorem 8 — mean and variance of the limiting opinions 𝓡* (root) and 𝓡 (neighbour) of the general recursion on a Galton–Watson tree
-- statement:
--   Consider the general recursion (1) on a delayed marked Galton–Watson tree with general signals $\mathcal W_{\mathbf i}^{(k)}=\xi(\mathcal X_{\mathbf i},U_{\mathbf i}^{(k)})$, $|\mathcal W_{\mathbf i}^{(k)}|\le d+c-\sum_{j=1}^{\mathcal N_{\mathbf i}}\mathcal C_{(\mathbf i,j)}$. Let $\mathcal R^*=\sum_{s\ge0}(\Delta^s\mathcal W^{(s)})(\varnothing)$ be the limiting opinion of the root and $\mathcal R=\sum_{s\ge0}(\Delta^s\mathcal W^{(s)})(1)$ that of its first neighbour, where $\Delta$ has weights $\mathcal C$ and self-weight $1-c-d$. Let
--   $$\rho_1^*=E\Big[\sum_{i=1}^{\mathcal N_\varnothing}\mathcal C_i\Big],\ \rho_1=E\Big[\sum_{i=1}^{\mathcal N_1}\mathcal C_{(1,i)}\Big],\ \rho_2^*=E\Big[\sum_{i=1}^{\mathcal N_\varnothing}\mathcal C_i^2\Big],\ \rho_2=E\Big[\sum_{i=1}^{\mathcal N_1}\mathcal C_{(1,i)}^2\Big],$$
--   $\mathcal Y_{\mathbf i}=E[\mathcal W_{\mathbf i}^{(s)}\mid\mathcal X_{\mathbf i}]$, $\mathcal V_{\mathbf i}=\mathrm{Var}(\mathcal W_{\mathbf i}^{(s)}\mid\mathcal X_{\mathbf i})$, $p_m=\sum_{s\ge0}\binom{s+m}{s}^2(1-c-d)^{2s}(c+d)^{2(m+1)}$, and let $T$ be Geometric on $\{0,1,2,\dots\}$ with $P(T=k)=\rho_2^k(1-\rho_2)$. Then
--   $$E[\mathcal R^*]=\frac{1}{c+d}E[\mathcal W_\varnothing]+\frac{\rho_1^*}{(c+d-\rho_1)(c+d)}E[\mathcal W_1],\qquad E[\mathcal R]=\frac{E[\mathcal W_1]}{c+d-\rho_1},$$
--   $$\begin{aligned}\mathrm{Var}(\mathcal R^*)={}&\mathrm{Var}\Big(\sum_{i=1}^{\mathcal N_\varnothing}\mathcal C_i\Big)\frac{E[\mathcal W_1]^2}{(c+d)^2(c+d-\rho_1)^2}+\frac{\mathrm{Var}(\mathcal Y_\varnothing)}{(c+d)^2}+\frac{2\,\mathrm{Cov}\big(\sum_{i=1}^{\mathcal N_\varnothing}\mathcal C_i,\mathcal Y_\varnothing\big)E[\mathcal W_1]}{(c+d)^2(c+d-\rho_1)}+\frac{E[\mathcal V_\varnothing]}{1-(1-c-d)^2}\\&+\rho_2^*\,\mathrm{Var}\Big(\sum_{i=1}^{\mathcal N_1}\mathcal C_{(1,i)}\Big)\frac{E[\mathcal W_1]^2}{(c+d)^2(c+d-\rho_1)^2((c+d)^2-\rho_2)}+\rho_2^*E[\mathcal V_1]\frac{1}{1-\rho_2}E\big[(c+d)^{-2(T+2)}p_{T+1}\big]\\&+\frac{\rho_2^*\mathrm{Var}(\mathcal Y_1)}{(c+d)^2((c+d)^2-\rho_2)}+\frac{2\rho_2^*\,\mathrm{Cov}\big(\sum_{i=1}^{\mathcal N_1}\mathcal C_{(1,i)},\mathcal Y_1\big)E[\mathcal W_1]}{(c+d)^2(c+d-\rho_1)((c+d)^2-\rho_2)},\end{aligned}$$
--   $$\begin{aligned}\mathrm{Var}(\mathcal R)={}&\mathrm{Var}\Big(\sum_{i=1}^{\mathcal N_1}\mathcal C_{(1,i)}\Big)\frac{E[\mathcal W_1]^2}{(c+d-\rho_1)^2((c+d)^2-\rho_2)}+E[\mathcal V_1]\frac{1}{1-\rho_2}E\big[(c+d)^{-2(T+1)}p_T\big]\\&+\frac{\mathrm{Var}(\mathcal Y_1)}{(c+d)^2-\rho_2}+\frac{2\,\mathrm{Cov}\big(\sum_{i=1}^{\mathcal N_1}\mathcal C_{(1,i)},\mathcal Y_1\big)E[\mathcal W_1]}{(c+d-\rho_1)((c+d)^2-\rho_2)}.\end{aligned}$$
--
--   The theorem gives closed forms for the first two moments of the stationary opinion of a typical vertex, with memory and with possibly empty in-neighbourhoods; Remark 10.2 and Proposition 6 specialize it.
--
--   **Formalization Note.** The paper assumes "the assumptions of Theorem 2" (a graph sequence converging to the tree); the statement concerns only the limit tree, so it is stated on the tree under the Section 5 standing assumptions, without the graph sequence (a generalization). $E[g(T)]$ is written as the series $\sum_k\rho_2^k(1-\rho_2)g(k)$ (`geomExp`); $(c+d)^{-2(T+2)}$ is `((c + d) ^ (2 * (k + 2)))⁻¹`. The side remark "$p_T\in(0,1)$" is not part of the statement (it fails at $c+d=1$, where $p_T=1$). No hypothesis is added for the denominators: $\rho_1\le c$ and $\rho_2\le c^2$ follow from the weights, so $c+d-\rho_1\ge d>0$, $(c+d)^2-\rho_2>0$, $1-\rho_2>0$ and $1-(1-c-d)^2>0$. All integrands are bounded, so the moments are genuine (no integrability junk). The paper's neighbour "$1$" is the label `[0]`. The signal map $\xi$ is passed as the signal map of `GWModel`, whose bound $|\xi|\le 1$ is implied by the hypothesis on $\xi$.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, pp. 32–33, Theorem 8

import Mathlib
import Definitions.Def_DirectedOpinion_Memory_Setting

namespace DirectedOpinion.Memory
open MeasureTheory ProbabilityTheory

/-- Theorem 8 (pp. 32–33): mean and variance of the limiting opinion 𝓡* of the root and 𝓡 of
a neighbour of the root, for the general recursion (1) with general bounded signals
𝓦_i^(k) = ξ(𝓧_i, U_i^(k)), on a delayed marked Galton–Watson tree. -/
theorem theorem_8 {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : DirectedOpinion.NoMemory.MarkFns M) (X : DirectedOpinion.NoMemory.Label → Ω → M)
    (U : DirectedOpinion.NoMemory.Label → ℕ → Ω → ℝ) (ξ : M → ℝ → ℝ) (c d : ℝ)
    (hGW : DirectedOpinion.NoMemory.GWModel P mk X U ξ c d)
    (hξ : ∀ x u, |ξ x u| ≤ d + c - ∑ j ∈ Finset.range (mk.N x), mk.C x j) :
    let ρ₁s := rho1star P mk X
    let ρ₁ := rho1 P mk X
    let ρ₂s := rho2star P mk X
    let ρ₂ := DirectedOpinion.NoMemory.rho2 P mk X
    let EW0 := ∫ ω, DirectedOpinion.NoMemory.Z X U ξ [] 0 ω ∂P
    let EW1 := ∫ ω, DirectedOpinion.NoMemory.Z X U ξ [0] 0 ω ∂P
    let Y := condMeanSig P X (DirectedOpinion.NoMemory.Z X U ξ)
    let V := condVarSig P X (DirectedOpinion.NoMemory.Z X U ξ)
    let Rstar := limOpinion mk X (DirectedOpinion.NoMemory.Z X U ξ) c d []
    let R := limOpinion mk X (DirectedOpinion.NoMemory.Z X U ξ) c d [0]
    (∫ ω, Rstar ω ∂P = 1 / (c + d) * EW0 + ρ₁s / ((c + d - ρ₁) * (c + d)) * EW1) ∧
    (∫ ω, R ω ∂P = EW1 / (c + d - ρ₁)) ∧
    variance Rstar P
      = variance (sumC mk X []) P * EW1 ^ 2 * (1 / ((c + d) ^ 2 * (c + d - ρ₁) ^ 2))
        + variance (Y []) P * (1 / (c + d) ^ 2)
        + 2 * covariance (sumC mk X []) (Y []) P * EW1 * (1 / ((c + d) ^ 2 * (c + d - ρ₁)))
        + (∫ ω, V [] ω ∂P) * (1 / (1 - (1 - c - d) ^ 2))
        + ρ₂s * variance (sumC mk X [0]) P * EW1 ^ 2
          * (1 / ((c + d) ^ 2 * (c + d - ρ₁) ^ 2 * ((c + d) ^ 2 - ρ₂)))
        + ρ₂s * (∫ ω, V [0] ω ∂P) * (1 / (1 - ρ₂))
          * geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1))
        + ρ₂s * variance (Y [0]) P * (1 / ((c + d) ^ 2 * ((c + d) ^ 2 - ρ₂)))
        + 2 * ρ₂s * covariance (sumC mk X [0]) (Y [0]) P * EW1
          * (1 / ((c + d) ^ 2 * (c + d - ρ₁) * ((c + d) ^ 2 - ρ₂))) ∧
    variance R P
      = variance (sumC mk X [0]) P * EW1 ^ 2 * (1 / (((c + d) - ρ₁) ^ 2 * ((c + d) ^ 2 - ρ₂)))
        + (∫ ω, V [0] ω ∂P) * (1 / (1 - ρ₂))
          * geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 1)))⁻¹ * pT c d k)
        + variance (Y [0]) P * (1 / ((c + d) ^ 2 - ρ₂))
        + 2 * covariance (sumC mk X [0]) (Y [0]) P * EW1
          * (1 / ((c + d - ρ₁) * ((c + d) ^ 2 - ρ₂))) := by sorry

end DirectedOpinion.Memory
