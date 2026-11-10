-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_middle_negligible
-- name    : CSSNearGV.Amplification.middle_negligible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:33.997933+00:00
-- url     : https://prove2.me/theorems/40d51f8f-e3a2-4d25-ac4f-eebf7ec3587b
-- title:
--   Theorem 5.2 — negligible middle contribution
-- statement:
--   Fix even $s\ge2$, $m\ge1$ and $\varepsilon>0$. Set $\tau=(\log n)^2/n$. For either order, the expected number of nonzero words having intermediate weight in $[\tau n,(1-\tau)n]$ after $m-1$ rounds and final weight at most $(\delta^{(m)}-\varepsilon)n$ or at least $(1-\delta^{(m)}+\varepsilon)n$ satisfies
--   $$\mathbb E[\#\text{such words}]\le\operatorname{negl}(n).$$
--   Negligibility retains every inverse polynomial. This bounds both final tails of the middle contribution.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - encoding: poly(n), soft-O and negligible estimates → eventual inequalities with positive constants, exponents and thresholds fixed before length and all weights; reason: the source leaves numerical prefactors unspecified; parameters s, m and epsilon are fixed before these constants
--   - reading: unbased log in the boundary cutoff → natural logarithm in T=(log n)^2; reason: the source leaves this base unstated; a fixed base changes the cutoff by a constant factor, and the boundary and negligible estimates retain their stated orders
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Theorem 5.2, printed pp.15–16 / PDF 17–18

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem middle_negligible (s : ℕ) (hs : 2 ≤ s) (he : Even s) (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
  Negligible s (fun b => middleCount s b m true ε) ∧
  Negligible s (fun b => middleCount s b m false ε) := by sorry

end CSSNearGV.Amplification
