-- Prove2me | Theorems.Thm_CustomHedge_Exist_ec_28
-- name    : CustomHedge.Exist.ec_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:55.104106+00:00
-- url     : https://prove2.me/theorems/26b42aad-38a5-4b20-985a-ec18d1be18a7
-- title:
--   (EC.28), p. ec25 — ‖E[φ(X)|F_I]‖₂ ≤ r_XI ‖φ(X)‖₂ for φ ∈ ℍ_X
-- statement:
--   Work in a combined custom hedging market under the standing assumptions. For every $\varphi\in\mathbb H_X$ (centered, square-integrable, $\mathcal F_X$-measurable),
--   $$\big\|\mathbb E[\varphi\mid\mathcal F_I]\big\|_2\le r_{XI}\,\|\varphi\|_2 .$$
--
--   The conditional expectation onto $\sigma(I)$ thus shrinks centered functionals of $X$ by at least the factor $r_{XI}$.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. ec25 (PDF 56), proof of Theorem 1, (EC.28)

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model

namespace CustomHedge.Exist

open MeasureTheory ProbabilityTheory

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- (EC.28), p. ec25: for `φ ∈ ℍ_X`, `‖E[φ | 𝓕_I]‖₂ ≤ r_XI ‖φ‖₂`. -/
theorem ec_28 (M : Market Ω EX EY EI) (hS : M.Standing) (φ : Ω → ℝ)
    (hφ : InCentered M.P M.FX φ) :
    l2norm M.P (condExp M.FI M.P φ) ≤ M.maxCorr * l2norm M.P φ := by sorry

end CustomHedge.Exist
