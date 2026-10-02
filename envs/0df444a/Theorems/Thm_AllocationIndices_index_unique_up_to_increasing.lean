-- Prove2me | Theorems.Thm_AllocationIndices_index_unique_up_to_increasing
-- name    : AllocationIndices.index_unique_up_to_increasing
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:49:38.314972+00:00
-- url     : https://prove2.me/theorems/2a63ce98-fb61-4f3c-9693-0b38aff8eab2
-- title:
--   Theorem 4.8: any index for the class of bandit processes with discount factor a is strictly increasing in ν(B, x)
-- statement:
--   **Theorem 4.8.** Any index for $\mathcal B_a$ ($0 < a < 1$), if there is one, must be a strictly increasing function of $\nu(B, x)$.
--
--   Formally: let $\mu$ assign a real number to every bandit process and state (an `IndexFunction`), and suppose $\mu$ is an index for every SFABP $\{B, \Lambda\}$ formed by a bandit process on a countable state space with bounded reward and a standard bandit process: every policy that continues an arm of maximal $\mu$-value at each decision time is optimal for that family. Then for any two bandit processes $B = (P, r)$ on $T$ and $B' = (P', r')$ on $T'$ (countable, bounded rewards) and states $x, x'$,
--   $$\nu(B, x) < \nu(B', x') \implies \mu(B, x) < \mu(B', x').$$
--
--   The hypothesis is weaker than the book's "index for $\mathcal B_a$" (optimality for every finite SFABP), since the proof only uses the two-member families $\{B, \Lambda(\lambda)\}$, so the statement is slightly stronger than printed; the conclusion compares processes on different state spaces, as the book's does.
--
--   The conclusion is the order form of "a strictly increasing function of $\nu$". The printed form also says that $\mu$ is a *function* of $\nu$, i.e. equal indices get equal $\mu$-values, and that part is not true. An index may break the ties within one level of $\nu$ in any way: $\mu = \nu$ with a different value on some of the bandit processes of index exactly $0$ still orders every family as $\nu$ does, up to ties, which Theorem 2.1 allows to be broken arbitrarily.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.5.2 p. 96, Theorem 4.8 with its proof (the SFABP {B, Λ})

import Definitions.Def_AllocationIndices_Superprocess

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem index_unique_up_to_increasing (μ : IndexFunction) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hμ : IsIndexForStandardPairs μ a)
    {T : Type} [MeasurableSpace T] [Countable T] [MeasurableSingletonClass T]
    (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ} (hr : BoundedReward r) (x : T)
    {T' : Type} [MeasurableSpace T'] [Countable T'] [MeasurableSingletonClass T']
    (P' : Kernel T' T') [IsMarkovKernel P'] {r' : T' → ℝ} (hr' : BoundedReward r') (x' : T')
    (hlt : gittinsIndex P r a x < gittinsIndex P' r' a x') :
    μ T P r x < μ T' P' r' x' := by sorry

end AllocationIndices
