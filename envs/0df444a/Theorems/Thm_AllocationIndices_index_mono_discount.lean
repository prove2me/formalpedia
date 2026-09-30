-- Prove2me | Theorems.Thm_AllocationIndices_index_mono_discount
-- name    : AllocationIndices.index_mono_discount
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:31:25.394985+00:00
-- url     : https://prove2.me/theorems/fcd58c9f-1f91-441e-b3f2-fd694d3f7fe1
-- title:
--   Theorem 2.3: the discrete-time Gittins index ν(B, x, a) is nondecreasing in the discount factor a
-- statement:
--   **Theorem 2.3.** The (discrete-time) Gittins index, $\nu(B, x, a)$, is nondecreasing in the discount factor $a$.
--
--   Formally: for a bandit process on a countable state space with bounded reward, every state $x$ and discount factors $0 < b \le a < 1$, $\nu(B, x, b) \le \nu(B, x, a)$, the index being (2.6) computed with the respective discount factor. (The proof in the text kills a $b$-discounted stopping time with an independent geometric clock of ratio $b/a$, which requires $b < a$; the displayed inequality there has its letters swapped.)
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §2.6.5 p. 32, Theorem 2.3 with its proof (randomized stopping times with a geometric kill)

import Definitions.Def_AllocationIndices_Index

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem index_mono_discount {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a b : ℝ} (hb0 : 0 < b) (hba : b ≤ a) (ha1 : a < 1) (x : S) :
    gittinsIndex P r b x ≤ gittinsIndex P r a x := by sorry

end AllocationIndices
