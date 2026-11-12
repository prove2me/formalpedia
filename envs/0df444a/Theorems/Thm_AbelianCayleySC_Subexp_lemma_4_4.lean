-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_lemma_4_4
-- name    : AbelianCayleySC.Subexp.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:46:24.726344+00:00
-- url     : https://prove2.me/theorems/44e9afcc-8a4c-4b30-b48f-ab41c9665af4
-- title:
--   Lemma 4.4 — cyclic distance against $1-\cos$
-- statement:
--   Let $b\ge2$ and $m\ge1$ be integers, and $|a|_m=\min_{k\in\mathbb Z}|a-km|$. For every non-negative integer $t$,
--
--   $$\frac{|t|_m}{m}\le\frac b4\Big(1-\cos\frac{2\pi t}{m}\Big)+\frac{|bt|_m}{bm}.$$
--
--   Averaged over the generators, this is the one-step inequality of Lemma 4.5.
--
--   Differences from the source: none.
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.10, Lemma 4.4

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
import Definitions.Def_AbelianCayleySC_Subexp_Cayley

open Finset

namespace AbelianCayleySC.Subexp

/-- **Lemma 4.4** (p.10). For integers `b ≥ 2`, `m ≥ 1` and every non-negative integer `t`,
`|t|_m / m ≤ (b/4)(1 − cos(2πt/m)) + |bt|_m / (bm)`. -/
theorem lemma_4_4 (b m : ℕ) (hb : 2 ≤ b) (hm : 0 < m) (t : ℕ) :
    modDist (m : ℝ) (t : ℝ) / (m : ℝ) ≤
      (b : ℝ) / 4 * (1 - Real.cos (2 * Real.pi * (t : ℝ) / (m : ℝ))) +
        modDist (m : ℝ) ((b : ℝ) * (t : ℝ)) / ((b : ℝ) * (m : ℝ)) := by sorry

end AbelianCayleySC.Subexp
