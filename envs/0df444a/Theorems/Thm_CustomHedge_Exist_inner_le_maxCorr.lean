-- Prove2me | Theorems.Thm_CustomHedge_Exist_inner_le_maxCorr
-- name    : CustomHedge.Exist.inner_le_maxCorr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:49.974523+00:00
-- url     : https://prove2.me/theorems/6140e96f-e036-4294-9ba8-0b6253bd3dd6
-- title:
--   Proof of Theorem 1, p. ec25 — ⟨E[φ(X)|F_I], ψ(I)⟩ ≤ r_XI ‖φ(X)‖₂ ‖ψ(I)‖₂ for φ ∈ ℍ_X, ψ ∈ ℍ_I
-- statement:
--   Work in a combined custom hedging market under the standing assumptions. For every $\varphi\in\mathbb H_X$ and $\psi\in\mathbb H_I$,
--   $$\big\langle\mathbb E[\varphi\mid\mathcal F_I],\psi\big\rangle=\mathbb E\big[\mathbb E[\varphi\mid\mathcal F_I]\,\psi\big]\le r_{XI}\,\|\varphi\|_2\,\|\psi\|_2,$$
--   where $r_{XI}$ is the maximal correlation (6) of $X$ and $I$.
--
--   This is the inequality linking the maximal correlation to the conditional-expectation operator between the two claim spaces. It holds without any assumption on the size of $r_{XI}$.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. ec25 (PDF 56), proof of Theorem 1

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model

namespace CustomHedge.Exist

open MeasureTheory ProbabilityTheory

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- Proof of Theorem 1, p. ec25: for `φ ∈ ℍ_X` and `ψ ∈ ℍ_I`,
`⟨E[φ | 𝓕_I], ψ⟩ ≤ r_XI ‖φ‖₂ ‖ψ‖₂`. -/
theorem inner_le_maxCorr (M : Market Ω EX EY EI) (hS : M.Standing) (φ ψ : Ω → ℝ)
    (hφ : InCentered M.P M.FX φ) (hψ : InCentered M.P M.FI ψ) :
    ∫ ω, condExp M.FI M.P φ ω * ψ ω ∂M.P ≤ M.maxCorr * l2norm M.P φ * l2norm M.P ψ := by sorry

end CustomHedge.Exist
