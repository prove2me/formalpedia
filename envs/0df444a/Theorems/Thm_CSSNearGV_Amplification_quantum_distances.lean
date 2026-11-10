-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_quantum_distances
-- name    : CSSNearGV.Amplification.quantum_distances
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:19:27.939198+00:00
-- url     : https://prove2.me/theorems/9b2d7901-fd47-4141-8c82-29342b6a603d
-- title:
--   Corollary 2.2 — simultaneous quantum X and Z distances
-- statement:
--   For every even $s\ge4$ and $\varepsilon>0$, some fixed $m\ge3$ gives a CSS code of exact rate $1-2/s$ with
--   $$d_X,d_Z\ge(h^{-1}(1/s)-\varepsilon)n$$
--   with probability at least $1-\widetilde O(n^{2-m})$. The probability is over the single independent uniform tuple defining $L$; the two distance events refer to the same code. Orthogonality, both stabilizer ranks, and the quantum dimension are conclusions.
--
--   This transfers the classical estimates to the quantum construction.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - encoding: poly(n), soft-O and negligible estimates → eventual inequalities with positive constants, exponents and thresholds fixed before length and all weights; reason: the source leaves numerical prefactors unspecified; parameters s, m and epsilon are fixed before these constants
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Corollary 2.2, printed p.8 / PDF 10; duality construction printed pp.6–7 / PDF 8–9

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem quantum_distances (s : ℕ) (hs : 4 ≤ s) (he : Even s) (ε : ℝ) (hε : 0 < ε) :
  ∃ m : ℕ, 3 ≤ m ∧
    (∀ b : ℕ, 1 ≤ b → ∀ π : Perms (s * b) m, cssParameters s b m π) ∧
    SoftBound s (fun b => probability fun π : Perms (s * b) m =>
      ¬ logicalBounds s b m π ((gv s - ε) * (s * b))) (2 - (m : ℝ)) := by sorry

end CSSNearGV.Amplification
