-- Prove2me | Theorems.Thm_CustomHedge_Exist_T_maps_centered
-- name    : CustomHedge.Exist.T_maps_centered
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:51.484255+00:00
-- url     : https://prove2.me/theorems/df6fed3e-1c92-4a8d-9869-34c08aac70e7
-- title:
--   Proof of Theorem 1, p. ec24 — E[T[Z]] = E[Z], T maps ℍ_X into itself, and Π₀ ∈ ℍ_X
-- statement:
--   Work in a combined custom hedging market under the standing assumptions, and let $T[Z]=\mathbb E\big[\mathbb E[Z\mid\mathcal F_I]\,\big|\,\mathcal F_X\big]$. Then:
--
--   1. for every integrable $Z$,
--   $$\mathbb E\big[T[Z]\big]=\mathbb E[Z];$$
--   2. $T$ maps the Hilbert subspace $\mathbb H_X$ of $P$-centered, $\mathcal F_X$-measurable, square-integrable random variables into itself;
--   3. $\Pi_0=-\mathbb E\big[\mathcal K-\mathbb E[\mathcal K\mid\mathcal F_I]\,\big|\,\mathcal F_X\big]$ belongs to $\mathbb H_X$.
--
--   These facts put the fixed-point equation (EC.25) in the abstract form $H_0=\Pi_0+T[H_0]$ on $\mathbb H_X$.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. ec24 (PDF 55), proof of Theorem 1, display before (EC.27)

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model

namespace CustomHedge.Exist

open MeasureTheory ProbabilityTheory

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- Proof of Theorem 1, p. ec24: `E[T[Z]] = E[Z]`; hence `T` maps `ℍ_X` (`P`-centered,
`𝓕_X`-measurable, `L²`) into itself; and `Π₀ ∈ ℍ_X`. -/
theorem T_maps_centered (M : Market Ω EX EY EI) (hS : M.Standing) :
    (∀ Z : Ω → ℝ, Integrable Z M.P → ∫ ω, M.T Z ω ∂M.P = ∫ ω, Z ω ∂M.P) ∧
      (∀ Z : Ω → ℝ, InCentered M.P M.FX Z → InCentered M.P M.FX (M.T Z)) ∧
      InCentered M.P M.FX M.Pi0X := by sorry

end CustomHedge.Exist
