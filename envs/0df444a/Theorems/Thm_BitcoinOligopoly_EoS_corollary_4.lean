-- Prove2me | Theorems.Thm_BitcoinOligopoly_EoS_corollary_4
-- name    : BitcoinOligopoly.EoS.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:27.773002+00:00
-- url     : https://prove2.me/theorems/0a33e6f6-6dfe-4248-9950-c2227f2a45aa
-- title:
--   Corollary 4 — a participating miner's minimum market share
-- statement:
--   Let $q$ be a pure Nash equilibrium of the economies-of-scale model, with $n\ge2$, $\alpha\ge1$, and positive unit costs. Every miner with positive market share has share at least
--
--   $$
--   x_i(q)\ge 1-\frac1\alpha.
--   $$
--
--   This bound constrains how many miners can participate when returns to investment are increasing.
-- source:
--   Arnosti & Weinberg, Bitcoin: A Natural Oligopoly, arXiv:1811.08572v1, p. 10 (PDF 11), Corollary 4

import Mathlib
import Definitions.Def_BitcoinOligopoly_EoS_Model

namespace BitcoinOligopoly.EoS

/-- Corollary 4, p. 10 (PDF 11). -/
theorem corollary_4 {n : ℕ} (P : Params n) (hP : P.Standing) (q : Fin n → ℝ)
    (hq : IsEquilibrium P q) :
    ∀ i, 0 < share P q i → 1 - 1 / P.α ≤ share P q i := by sorry

end BitcoinOligopoly.EoS
