-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_eventually_zero
-- name    : CSSNearGV.Amplification.eventually_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:32.058198+00:00
-- url     : https://prove2.me/theorems/faa644ef-ec3d-496d-b1f7-76aa2334ae81
-- title:
--   Proposition 4.5 — every sub-GV point eventually has zero shape
-- statement:
--   For even $s\ge2$ and every spectral-domain point $0\le\gamma<h^{-1}(1/s)$, $$\exists m\ge0:\ r_A^{(m)}(\gamma)=0.$$ This supplies the pointwise ingredient in threshold convergence.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Proposition 4.5, printed p.14 / PDF 16

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem eventually_zero (s : ℕ) (hs : 2 ≤ s) (he : Even s) (γ : ℝ) (hγ : 0 ≤ γ) (hgv : γ < gv s) : ∃ m : ℕ, shapeA s m γ = 0 := by sorry

end CSSNearGV.Amplification
