-- Prove2me | Theorems.Thm_DivQuotient_remark_EC_2
-- name    : DivQuotient.remark_EC_2
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:52:18.481987+00:00
-- url     : https://prove2.me/theorems/3d0c3086-633e-48be-9e00-c5b804d285fb
-- title:
--   Remark EC.2 — a non-linear sub-linear $\phi$ has $\phi(Y)+\phi(-Y)>0$ for some $Y$
-- statement:
--   Let $\phi:\mathcal X\to\mathbb R$ be a sub-linear risk measure (subadditive and positively homogeneous) that is not linear. Then there exists $Y\in\mathcal X$ with
--
--   $$
--   \phi(Y)+\phi(-Y)>0.
--   $$
--
--   The paper states this for non-linear coherent risk measures, and uses the same argument for sub-linear ones in the proof of Proposition 1. It supplies the asymmetric position used to realise every value of DQ in $[0,1]$ and to build convex combinations in the proof of Theorem 2.
--
--   Differences from the source:
--   - generalization: φ a non-linear coherent risk measure → φ non-linear and sub-linear ([SA] and [PH]); reason: the argument uses only [SA] and [PH]; the proof of Proposition 1 (p.44) applies it to sub-linear measures; coherent measures are sub-linear
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, Remark EC.2, p.35; used for sub-linear measures in the proof of Proposition 1, p.44

import Mathlib
import Definitions.Def_DivQuotient_RiskMeasure

open MeasureTheory

namespace DivQuotient

/-- **Remark EC.2** (Han–Lin–Wang, arXiv:2206.13679v6, p.35): "For a non-linear coherent risk
measure φ, there exists Y ∈ 𝒳 such that φ(Y) + φ(−Y) > 0."

Stated for sub-linear (subadditive and positively homogeneous) `φ`, as used in the proof of
Proposition 1 (p.44, "following the argument of Remark EC.2"); a coherent `φ` is sub-linear. -/
theorem remark_EC_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (φ : Lp ℝ ⊤ P → ℝ) (hφ : IsSublinear φ) (hnl : ¬ IsLinear φ) :
    ∃ Y : Lp ℝ ⊤ P, 0 < φ Y + φ (-Y) := by sorry

end DivQuotient
