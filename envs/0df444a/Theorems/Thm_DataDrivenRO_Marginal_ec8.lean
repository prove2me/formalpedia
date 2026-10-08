-- Prove2me | Theorems.Thm_DataDrivenRO_Marginal_ec8
-- name    : DataDrivenRO.Marginal.ec8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:22:06.605612+00:00
-- url     : https://prove2.me/theorems/adec9373-9ff4-4cbd-b52f-65bcf0dc9f27
-- title:
--   (EC.8), p. ec5 — VaR_ε(v) ≤ Σ_{vᵢ>0} vᵢû^(s)_i + Σ_{vᵢ≤0} vᵢû^(N−s+1)_i for every ℙ ∈ 𝒫^M
-- statement:
--   Let $d\ge1$, $0<\epsilon<1$, $0<\alpha<1$, fix a sample and the a priori box, and let $\mathbb P\in\mathcal P^M$, i.e. $\mathbb P$ is a probability measure on the box with $\mathrm{VaR}^{\mathbb P}_{\epsilon/d}(\mathbf e_i)\le\hat u^{(s)}_i$ and $\mathrm{VaR}^{\mathbb P}_{\epsilon/d}(-\mathbf e_i)\le-\hat u^{(N-s+1)}_i$ for every $i$. Then for every $\mathbf v\in\mathbb R^d$,
--   $$\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)\le\sum_{i:v_i>0}v_i\hat u^{(s)}_i+\sum_{i:v_i\le0}v_i\hat u^{(N-s+1)}_i .$$
--
--   This is the worst-case Value at Risk bound over the confidence region (Step 2 of the schema), obtained in the paper by combining the weak Embrechts bound with positive homogeneity of VaR.
--
--   **Formalization Note** The page writes (EC.8) as $\sup_{\mathcal P^M}\mathrm{VaR}\le\sup_{\mathcal P^M}\sum_i\mathrm{VaR}_{\epsilon/d}(v_i\mathbf e_i)=\dots$; the statement here is the resulting inequality for each $\mathbb P\in\mathcal P^M$. Only "$\le$" is used in the proof of Theorem 7 and only "$\le$" is stated; the middle "$=$" is not claimed.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.5, (EC.8), p. ec5

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

open MeasureTheory

namespace DataDrivenRO.Marginal

/-- (EC.8), p. ec5: for every `ℙ ∈ 𝒫^M` and every `v`,
`VaR^ℙ_ε(v) ≤ ∑_{i : vᵢ > 0} vᵢ û^(s)_i + ∑_{i : vᵢ ≤ 0} vᵢ û^(N−s+1)_i`. -/
theorem ec8 {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hα0 : 0 < α) (hα1 : α < 1) (lo hi : Fin d → ℝ) (S : Fin N → Fin d → ℝ)
    (P : Measure (Fin d → ℝ)) (hP : P ∈ PM S lo hi ε α) (v : Fin d → ℝ) :
    VaR P ε v ≤ ∑ i, (if 0 < v i then v i * uhat S lo hi i (sIndex N d ε α)
      else v i * uhat S lo hi i (N + 1 - sIndex N d ε α)) := by sorry

end DataDrivenRO.Marginal
