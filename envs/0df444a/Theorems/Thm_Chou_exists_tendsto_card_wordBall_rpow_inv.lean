-- Prove2me | Theorems.Thm_Chou_exists_tendsto_card_wordBall_rpow_inv
-- name    : Chou.exists_tendsto_card_wordBall_rpow_inv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:57:47.195578+00:00
-- url     : https://prove2.me/theorems/53210fa0-c328-403b-9865-4f926ae7c5e4
-- title:
--   Milnor: the growth rate $\lim |B(n)|^{1/n}$ exists
-- statement:
--   For a finite generating set $S$ of $G$, writing $B(n)$ for the set of products of at most $n$
--   elements of $S \cup S^{-1}$, the sequence $|B(n)|^{1/n}$ converges to some real number.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 399 (Milnor [16], cited)

import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

/-- p. 399, Milnor's theorem as Chou states it: for a finite generating set `S`, the growth rate
`lim |B(n)|^{1/n}` exists, where `B(n)` is the ball of radius `n` of the bundle. -/
theorem exists_tendsto_card_wordBall_rpow_inv {G : Type*} [Group G] (S : Finset G)
    (hS : Subgroup.closure (S : Set G) = ⊤) :
    ∃ v : ℝ, Filter.Tendsto (fun n : ℕ => (Nat.card (wordBall (S : Set G) n) : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds v) := by
  sorry

end Chou
