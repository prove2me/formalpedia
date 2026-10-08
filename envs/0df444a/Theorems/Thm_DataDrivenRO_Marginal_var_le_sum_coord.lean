-- Prove2me | Theorems.Thm_DataDrivenRO_Marginal_var_le_sum_coord
-- name    : DataDrivenRO.Marginal.var_le_sum_coord
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:21:39.010826+00:00
-- url     : https://prove2.me/theorems/3b2fc784-06fb-4ab5-9b29-918d647866fb
-- title:
--   p. 21 — weak Embrechts bound VaR_ε(v) ≤ Σᵢ VaR_{ε/d}(vᵢeᵢ)
-- statement:
--   Let $d\ge1$, $0<\epsilon<1$ and let $\mathbb P$ be any probability measure on $\mathbb R^d$ (no independence or other assumption on its marginals). Then for every $\mathbf v\in\mathbb R^d$,
--   $$\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)\le\sum_{i=1}^d\mathrm{VaR}^{\mathbb P}_{\epsilon/d}(v_i\mathbf e_i).$$
--
--   This is the bound of Embrechts et al. (27) with the choice $\lambda_i=\epsilon/d$. It reduces the Value at Risk of $\tilde{\mathbf u}^T\mathbf v$ to quantities that depend on the marginals of $\mathbb P$ only, which is what makes marginal samples sufficient.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, §6, (27) and the sentence after it, p. 21

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

open MeasureTheory

namespace DataDrivenRO.Marginal

/-- p. 21, the weaker form of (27) with `λᵢ = ε/d`:
`VaR^ℙ_ε(v) ≤ ∑ᵢ VaR^ℙ_{ε/d}(vᵢ eᵢ)` for every probability measure `ℙ` on `ℝᵈ`. -/
theorem var_le_sum_coord {d : ℕ} (hd : 0 < d) (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) :
    VaR P ε v ≤ ∑ i, VaR P (ε / d) (Pi.single i (v i)) := by sorry

end DataDrivenRO.Marginal
