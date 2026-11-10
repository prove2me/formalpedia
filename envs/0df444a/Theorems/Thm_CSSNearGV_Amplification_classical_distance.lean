-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_classical_distance
-- name    : CSSNearGV.Amplification.classical_distance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:19:12.029875+00:00
-- url     : https://prove2.me/theorems/0c0d754b-4e4e-474f-913b-f4b043168f4e
-- title:
--   Theorem 2.1 — both classical interleaver ensembles
-- statement:
--   For every even $s\ge2$, there is a nondecreasing positive sequence $\delta^{(m)}$, $m\ge2$, converging to $\delta_{\rm GV}=h^{-1}(1/s)$. For every $\varepsilon>0$, both classical ensembles have exact rate $1-1/s$, and
--   $$\Pr[d_{DA}/n\ge\delta^{(m)}-\varepsilon]\ge1-\widetilde O(n^{1-m})\quad(m\ge2),$$
--   $$\Pr[d_{AD}/n\ge\delta^{(m)}-\varepsilon]\ge1-\widetilde O(n^{2-m})\quad(m\ge3).$$
--   The sequence is the source's spectral threshold sequence, and the rates hold for every permutation tuple. This retains the classical $s=2$ case needed for the complete source theorem.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - encoding: poly(n), soft-O and negligible estimates → eventual inequalities with positive constants, exponents and thresholds fixed before length and all weights; reason: the source leaves numerical prefactors unspecified; parameters s, m and epsilon are fixed before these constants
--   - reading: increasing and decreasing → nondecreasing and nonincreasing; reason: Proposition 4.2 explicitly gives delta^(m) >= delta^(m-1); the source does not assert a strict increase at every round
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Theorem 2.1, printed p.8 / PDF 10

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem classical_distance (s : ℕ) (hs : 2 ≤ s) (he : Even s) :
  Monotone (fun m : ℕ => delta s (m + 2)) ∧
  (∀ m : ℕ, 2 ≤ m → 0 < delta s m) ∧
  Filter.Tendsto (delta s) Filter.atTop (nhds (gv s)) ∧
  (∀ ε : ℝ, 0 < ε →
    (∀ m : ℕ, 2 ≤ m → ClassicalTail s m false ε (1 - (m : ℝ))) ∧
    (∀ m : ℕ, 3 ≤ m → ClassicalTail s m true ε (2 - (m : ℝ)))) := by sorry

end CSSNearGV.Amplification
