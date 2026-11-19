-- Prove2me | Theorems.Thm_AJOnline_KTaxi2_memory_helps
-- name    : AJOnline.KTaxi2.memory_helps
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:38:45.551437+00:00
-- url     : https://prove2.me/theorems/1c90e304-ffda-4448-ad03-8b2aa29e2226
-- title:
--   Memory helps: a never-stopping 9-competitive behaviour strategy for two taxis
-- statement:
--   For every labelled start $x_0\in\mathbb R^2$ there are a behaviour strategy $\beta$ on the 2-taxi game from $x_0$ and a constant $b\ge0$ satisfying two conditions:
--
--   1. $\beta$ never stops;
--   2. for every request script,
--   $$\mathbb E[\mathrm{alg}]\le 9\,\mathbb E[\mathrm{opt}]+b .$$
--
--   Together with the goal, this separates history-dependent from history-free strategies in one game.
-- source:
--   AJ form of C. Coester, Y. Huang, T.-Y. Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Theorem 1.1 (randomised 9^{k-1}-competitive algorithm on every metric, against adaptive online adversaries), at k = 2 on the real line; competitiveness against adaptive online adversaries implies it against oblivious ones

import Mathlib
import Definitions.Def_AJOnline_KTaxi2
import Definitions.Def_AJGames_BehTensor

namespace AJOnline.KTaxi2

open AJGames KTaxi.Competitive.Supplement
open scoped ENNReal NNReal

/-- **Memory helps.** From every labelled start `x₀` there is a behaviour strategy on the 2-taxi
game (using the whole history) that never stops and is randomised-competitive with ratio `9`
against oblivious adversaries. -/
theorem memory_helps (x₀ : Fin 2 → ℝ) :
    ∃ (β : BehStrategy (game x₀)) (b : ℝ≥0), β.NonStop ∧ RandCompetitive (costed x₀) β 9 b := by sorry

end AJOnline.KTaxi2
