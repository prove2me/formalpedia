-- Prove2me | Theorems.Thm_ExpanderBIS_Potts_eq_5
-- name    : ExpanderBIS.Potts.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:31.670911+00:00
-- url     : https://prove2.me/theorems/9fc1e70d-4ddd-4b6d-a398-0c268dd1b8f9
-- title:
--   Inequality (5) — the per-vertex polymer sum
-- statement:
--   Let $G$ be a finite $\alpha$-expander of maximum degree at most $\Delta$, with $\alpha>0$, $\Delta\ge3$, and $q\ge2$. At inverse temperature $\beta\ge(4+2\log(q\Delta))/\alpha$, every vertex $v$ satisfies
--
--   $$
--   \sum_{\gamma\ni v}e^{(2-\alpha\beta+\log(q-1))|\gamma|}
--   \le\frac1{\Delta+1},
--   $$
--
--   where the sum ranges over the defined polymers of $G$. This is the local estimate used to bound the total weight of polymers incompatible with a given polymer.
--
--   **Formalization Note** $\log$ is natural logarithm. The bound includes the graph's edge-expansion and degree hypotheses from the section's standing assumptions.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 16, equation (5) and subsequent displayed estimate

import Mathlib
import Definitions.Def_ExpanderBIS_Potts_Setting

namespace ExpanderBIS.Potts

open Finset

/-- Inequality (5) in §3.2, p. 16. -/
theorem eq_5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (α β : ℝ) (Δ q : ℕ)
    (hα : 0 < α) (hΔ : 3 ≤ Δ) (hq : 2 ≤ q)
    (hdeg : ∀ v, G.degree v ≤ Δ) (hG : IsExpander G α)
    (hβ : (4 + 2 * Real.log ((q * Δ : ℕ) : ℝ)) / α ≤ β)
    (v : V) :
    (∑ γ ∈ (polymers G).filter (fun γ => v ∈ γ),
      Real.exp ((2 - α * β + Real.log (((q - 1 : ℕ) : ℝ))) * (#γ : ℝ))) ≤
      (1 : ℝ) / (Δ + 1) := by sorry

end ExpanderBIS.Potts
