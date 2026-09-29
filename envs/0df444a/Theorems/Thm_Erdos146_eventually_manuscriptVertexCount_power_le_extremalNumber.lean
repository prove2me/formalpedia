-- Prove2me | Theorems.Thm_Erdos146_eventually_manuscriptVertexCount_power_le_extremalNumber
-- name    : Erdos146.eventually_manuscriptVertexCount_power_le_extremalNumber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:54:31.25293+00:00
-- url     : https://prove2.me/theorems/88158922-b17b-48c1-92ae-65a7e071a8c6
-- title:
--   The extremal number eventually exceeds $n^{3/2+\varepsilon}$
-- statement:
--   Step in assembling the lower bound of Theorem 1.2 from the sampled host: a graph that is $H$-free with probability $1 - o(1)$ (Proposition 8.1) and has $\Omega(n^{3/2+\varepsilon})$ edges by a second-moment argument witnesses $\mathrm{ex}(n, H) \ge c\,n^{3/2+\varepsilon}$. Eventually $\mathrm{ex}(n, H) \ge n^{3/2+\varepsilon}$ along the constructed orders; padding then extends the bound to every sufficiently large $n$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L18310-L18328

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.eventually_manuscriptVertexCount_power_le_extremalNumber :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        (manuscriptVertexCount dimension : ℝ) ^
            manuscriptExtremalPower ≤
          (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension)
            (pairGraphOverFin baseSize depth) : ℝ) := by sorry
