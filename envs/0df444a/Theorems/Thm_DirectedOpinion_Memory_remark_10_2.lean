-- Prove2me | Theorems.Thm_DirectedOpinion_Memory_remark_10_2
-- name    : DirectedOpinion.Memory.remark_10_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:53.223593+00:00
-- url     : https://prove2.me/theorems/a90f0748-c1fd-40ff-aca2-5f2988673f62
-- title:
--   Remark 10.2 — with Section 5.1 signals and 𝓝_∅, 𝓝₁ > 0 a.s., mean and variance of the root opinion of the general recursion (mean corrected by the factor d)
-- statement:
--   Consider the general recursion (8) on a delayed marked Galton–Watson tree with the Section 5.1 signals $\mathcal W_{\mathbf i}^{(k)}=d\mathcal Z_{\mathbf i}^{(k)}+\mathcal Q_{\mathbf i}\big(c-\sum_{j=1}^{\mathcal N_{\mathbf i}}\mathcal C_{(\mathbf i,j)}\big)$, and let $\mathcal R^*$ be the limiting opinion of the root (the opinion called $\mathcal M^*$ in Proposition 6). Suppose $P(\mathcal N_\varnothing>0)=P(\mathcal N_1>0)=1$. With $\rho_1^*,\rho_1,\rho_2^*,\rho_2,p_m$ and the Geometric variable $T$ as in Theorem 8,
--   $$E[\mathcal R^*]=\frac{d}{c+d}E[\mathcal Z_\varnothing]+\frac{d\,\rho_1^*}{(c+d-\rho_1)(c+d)}E[\mathcal Z_1],$$
--   $$\begin{aligned}\mathrm{Var}(\mathcal R^*)={}&\frac{d^2}{(c+d)^2}\mathrm{Var}(\mathcal Z_\varnothing)+\frac{d^2\rho_2^*}{(c+d)^2((c+d)^2-\rho_2)}\mathrm{Var}(\mathcal Z_1)+\frac{2d^2(c+d-1)}{(c+d)^2(2-(c+d))}E[\mathrm{Var}(\mathcal Z_\varnothing\mid\mathcal X_\varnothing)]\\&+d^2\rho_2^*\Big(\frac{1}{1-\rho_2}E\big[(c+d)^{-2(T+2)}p_{T+1}\big]-\frac{1}{(c+d)^2((c+d)^2-\rho_2)}\Big)E[\mathrm{Var}(\mathcal Z_1\mid\mathcal X_1)].\end{aligned}$$
--
--   The variance formula separates the contribution of the conditional variances of the media signals; it is the expression the proof of Proposition 6 compares with (15).
--
--   **Formalization Note.** The printed mean reads $\frac{1}{c+d}E[\mathcal Z_\varnothing]+\frac{\rho_1^*}{(c+d-\rho_1)(c+d)}E[\mathcal Z_1]$, without the factor $d$. Since $\mathcal W=d\mathcal Z$ almost surely here, Theorem 8 gives the mean stated above; the printed form contradicts Proposition 4 at $c+d=1$ and gives $E[\mathcal Z]/d$ instead of $E[\mathcal Z]$ on the path tree. The corrected mean is stated; the variance is as printed. Here $\mathcal R^*$ is the general-recursion root opinion `Mstar` (Proposition 6's $\mathcal M^*$), not the no-memory `RstarNoMem`. The paper's hypotheses "of Theorem 2" are replaced by the limit tree with the Section 5 standing assumptions (as in Theorem 8). $E[g(T)]$ is the series `geomExp`. The denominators are positive: with $\mathcal N_1>0$ a.s., $\rho_1=c$ so $c+d-\rho_1=d$; $\rho_2\le c^2<(c+d)^2\le1$; $2-(c+d)\ge1$.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, pp. 33–34, Remarks 10, item 2

import Mathlib
import Definitions.Def_DirectedOpinion_Memory_Setting

namespace DirectedOpinion.Memory
open MeasureTheory ProbabilityTheory

/-- Remark 10.2 (pp. 33–34), mean corrected by the factor d (printed slip): with the
Section 5.1 signals and 𝓝_∅, 𝓝₁ > 0 a.s., the mean and variance of the root opinion of the
general recursion (called 𝓡* in the appendix, 𝓜* in Proposition 6). -/
theorem remark_10_2 {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : DirectedOpinion.NoMemory.MarkFns M) (X : DirectedOpinion.NoMemory.Label → Ω → M)
    (U : DirectedOpinion.NoMemory.Label → ℕ → Ω → ℝ) (ζ : M → ℝ → ℝ) (c d : ℝ)
    (hGW : DirectedOpinion.NoMemory.GWModel P mk X U ζ c d)
    (hN0 : ∀ᵐ ω ∂P, 0 < mk.N (X [] ω)) (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) :
    let ρ₁s := rho1star P mk X
    let ρ₁ := rho1 P mk X
    let ρ₂s := rho2star P mk X
    let ρ₂ := DirectedOpinion.NoMemory.rho2 P mk X
    let Rstar := Mstar mk X U ζ c d
    (∫ ω, Rstar ω ∂P
      = d / (c + d) * ∫ ω, DirectedOpinion.NoMemory.Z X U ζ [] 0 ω ∂P
        + d * ρ₁s / ((c + d - ρ₁) * (c + d)) * ∫ ω, DirectedOpinion.NoMemory.Z X U ζ [0] 0 ω ∂P) ∧
    variance Rstar P
      = d ^ 2 / (c + d) ^ 2 * variance (DirectedOpinion.NoMemory.Z X U ζ [] 0) P
        + d ^ 2 * ρ₂s / ((c + d) ^ 2 * ((c + d) ^ 2 - ρ₂)) * variance (DirectedOpinion.NoMemory.Z X U ζ [0] 0) P
        + 2 * d ^ 2 * (c + d - 1) / ((c + d) ^ 2 * (2 - (c + d)))
          * ∫ ω, condVarSig P X (DirectedOpinion.NoMemory.Z X U ζ) [] ω ∂P
        + d ^ 2 * ρ₂s
          * (1 / (1 - ρ₂) * geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1))
            - 1 / ((c + d) ^ 2 * ((c + d) ^ 2 - ρ₂)))
          * ∫ ω, condVarSig P X (DirectedOpinion.NoMemory.Z X U ζ) [0] ω ∂P := by sorry

end DirectedOpinion.Memory
