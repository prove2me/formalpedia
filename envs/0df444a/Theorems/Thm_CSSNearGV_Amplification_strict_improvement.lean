-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_strict_improvement
-- name    : CSSNearGV.Amplification.strict_improvement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:32.242204+00:00
-- url     : https://prove2.me/theorems/6bacb7a1-4b5c-4439-b978-29d0145f831a
-- title:
--   Proposition 5.5 — strict spectral improvement away from the boundary
-- statement:
--   Fix $0<\delta_1<\delta_2<1/2$ and let
--   $$c=\min\left\{\frac{1-2\delta_2}{\ln2},\log_2\frac{1-\delta_2}{\delta_2}\right\}>0.$$
--   For every $\alpha\in[0,1]$,
--   $$g(\alpha,\delta_2)-g(\alpha,\delta_1)\ge c\min(\alpha,1-\alpha)(\delta_2-\delta_1).$$
--   The displayed value of $c$ is the source proof's choice; it is independent of $\alpha$ and $n$. This gives uniform improvement away from the boundary.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - encoding: a constant c independent of alpha and n → the positive minimum displayed in the proof; reason: the proof explicitly supplies this witness
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Proposition 5.5 and its proof, printed p.18 / PDF 20

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem strict_improvement (δ₁ δ₂ : ℝ) (h₁ : 0 < δ₁) (h₁₂ : δ₁ < δ₂) (h₂ : δ₂ < 1 / 2) :
  let c := min ((1 - 2 * δ₂) / Real.log 2) (Real.logb 2 ((1 - δ₂) / δ₂))
  0 < c ∧ ∀ α ∈ Set.Icc (0 : ℝ) 1,
    c * min α (1 - α) * (δ₂ - δ₁) ≤ g α δ₂ - g α δ₁ := by sorry

end CSSNearGV.Amplification
