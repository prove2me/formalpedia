-- Prove2me | Theorems.Thm_ExpanderBIS_Potts_weight_le
-- name    : ExpanderBIS.Potts.weight_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:51.064993+00:00
-- url     : https://prove2.me/theorems/e42ba551-cf30-4026-8bc3-47bfd98a72e6
-- title:
--   §3.2 weight bound — exponential decay of Potts polymer weights
-- statement:
--   Let $G$ be a finite $\alpha$-expander, let $\gamma$ be one of its polymers, and suppose $\alpha>0$, $\beta\ge0$, and $q\ge2$. The polymer weight satisfies
--
--   $$
--   w_\gamma\le e^{-\beta\alpha|\gamma|}(q-1)^{|\gamma|}.
--   $$
--
--   This is the decay estimate used to check the Kotecký–Preiss condition. The polymer weight includes both edges within $\gamma$ and edges crossing its boundary.
--
--   **Formalization Note** The nonnegative-temperature hypothesis makes the displayed bound valid, and is implied by the threshold of Theorem 3. The polymer membership condition supplies connectedness and $2|\gamma|\le|V(G)|$.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 15, §3.2, displayed bound on w_γ

import Mathlib
import Definitions.Def_ExpanderBIS_Potts_Setting

namespace ExpanderBIS.Potts

open Finset

/-- The polymer-weight bound in §3.2, p. 15. -/
theorem weight_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (α β : ℝ) (q : ℕ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hq : 2 ≤ q) (hG : IsExpander G α)
    (γ : Finset V) (hγ : γ ∈ polymers G) :
    weight G q β γ ≤
      Real.exp (-β * α * (#γ : ℝ)) * ((q - 1 : ℕ) : ℝ) ^ #γ := by sorry

end ExpanderBIS.Potts
