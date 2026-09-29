-- Prove2me | Theorems.Thm_Chou_hasExponentialGrowth_iff_forall
-- name    : Chou.hasExponentialGrowth_iff_forall
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:57:23.574733+00:00
-- url     : https://prove2.me/theorems/98d7a94e-5d5c-487d-bba3-1e13c0774aee
-- title:
--   Wolf: exponential growth does not depend on the generating set
-- statement:
--   For a finitely generated group $G$: $G$ has exponential growth (with respect to some finite
--   generating set) if and only if for every finite generating set $S$ there is $c > 1$ with
--   $|\text{wordBall}(S, n)| \ge c^n$ for all $n$.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 399 ("The conditions mentioned above do not depend on the choice of the finite generating set F, cf. Wolf")

import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

/-- p. 399 (Wolf): exponential growth does not depend on the choice of the finite generating
set. -/
theorem hasExponentialGrowth_iff_forall {G : Type*} [Group G] [Group.FG G] :
    HasExponentialGrowth G ↔
      ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ →
        ∃ c : ℝ, 1 < c ∧ ∀ n : ℕ, c ^ n ≤ (Nat.card (wordBall (S : Set G) n) : ℝ) := by
  sorry

end Chou
