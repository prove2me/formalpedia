-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_threshold_convergence
-- name    : CSSNearGV.Amplification.threshold_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:36.390661+00:00
-- url     : https://prove2.me/theorems/37f71cd2-14d0-4541-ac95-d2044b5d7ce5
-- title:
--   Theorem 4.1 — threshold convergence to GV
-- statement:
--   For every even $s\ge2$, let $\delta_{\rm GV}$ be the unique root of $h(t)=1/s$ in $[0,1/2]$. Then
--   $$\lim_{m\to\infty}\delta^{(m)}=\delta_{\rm GV}.$$
--   The root property and uniqueness are conclusions as well, ensuring that the inverse-entropy representation has the intended meaning.
--
--   This result supplies the full inverse-entropy constant in the headline theorem.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - encoding: maxima and inverse-entropy root used in Definitions 1.2 and 3.2–3.4 → supremum/infimum definitions with attainment and the root property included as conclusions; reason: well-posedness is proved rather than assumed or silently delegated to total-function defaults
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Theorem 4.1, printed p.12 / PDF 14; Definition 1.2 and Section 4

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem threshold_convergence (s : ℕ) (hs : 2 ≤ s) (he : Even s) :
  gv s ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ entropy (gv s) = 1 / (s : ℝ) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), entropy t = 1 / (s : ℝ) → t = gv s) ∧
  Filter.Tendsto (delta s) Filter.atTop (nhds (gv s)) := by sorry

end CSSNearGV.Amplification
