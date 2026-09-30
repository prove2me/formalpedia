-- Prove2me | Theorems.Thm_AllocationIndices_stoppable_conditionD
-- name    : AllocationIndices.stoppable_conditionD
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T02:48:33.520301+00:00
-- url     : https://prove2.me/theorems/48e60a0d-4630-4794-bb2f-2a396b648979
-- title:
--   Lemma 4.4: a stoppable bandit process with an improving stopping option satisfies Condition D
-- statement:
--   **Lemma 4.4.** Condition D holds for a stoppable bandit process $S$ with an improving stopping option.
--
--   Formally: for a bandit process $(P, r)$ on a countable state space with bounded reward, a bounded stopping parameter $\mu$, $a \in (0,1)$, such that $\mu(x(t))$ is almost surely nondecreasing in process time from every initial state, the stoppable bandit process (continuation control: move by $P$ and collect $r(x)$; stop control: state unchanged, collect $\mu(x)$) satisfies Condition D. Boundedness of $\mu$ is the standing bounded-rewards assumption applied to the stop control.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.4 p. 88, Lemma 4.4 with its proof on p. 89

import Definitions.Def_AllocationIndices_Superprocess

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem stoppable_conditionD {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r μ : S → ℝ}
    (hr : BoundedReward r) (hμ : BoundedReward μ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (himp : HasImprovingStoppingOption P μ) :
    ConditionD (stoppable P r μ) a := by sorry

end AllocationIndices
