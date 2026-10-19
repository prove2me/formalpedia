-- Prove2me | Theorems.Thm_CustomHedge_Exist_T_norm_le
-- name    : CustomHedge.Exist.T_norm_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:54.799776+00:00
-- url     : https://prove2.me/theorems/f902101c-4914-42e5-b461-abd44213dada
-- title:
--   Proof of Theorem 1, p. ec25 — ‖T[φ]‖₂ ≤ r_XI ‖φ‖₂ on ℍ_X, i.e. ‖T‖ ≤ r_XI
-- statement:
--   Work in a combined custom hedging market under the standing assumptions, and let $T[Z]=\mathbb E\big[\mathbb E[Z\mid\mathcal F_I]\,\big|\,\mathcal F_X\big]$. For every $\varphi\in\mathbb H_X$,
--   $$\Big\|\mathbb E\big[\mathbb E[\varphi\mid\mathcal F_I]\,\big|\,\mathcal F_X\big]\Big\|_2\le r_{XI}\,\|\varphi\|_2 ,$$
--   so the operator norm of $T$ on $\mathbb H_X$ is at most $r_{XI}$.
--
--   When $r_{XI}<1$ this makes $T$ a contraction of $\mathbb H_X$.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. ec25 (PDF 56), proof of Theorem 1

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model

namespace CustomHedge.Exist

open MeasureTheory ProbabilityTheory

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- Proof of Theorem 1, p. ec25: `‖E[E[φ | 𝓕_I] | 𝓕_X]‖₂ ≤ r_XI ‖φ‖₂` for all
`φ ∈ ℍ_X`; hence `‖T‖ ≤ r_XI` on `ℍ_X`. -/
theorem T_norm_le (M : Market Ω EX EY EI) (hS : M.Standing) (φ : Ω → ℝ)
    (hφ : InCentered M.P M.FX φ) :
    l2norm M.P (M.T φ) ≤ M.maxCorr * l2norm M.P φ := by sorry

end CustomHedge.Exist
