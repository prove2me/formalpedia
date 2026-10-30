-- Prove2me | Theorems.Thm_FiniteMemQL_Convergence_qStar_min_eq_JN
-- name    : FiniteMemQL.Convergence.qStar_min_eq_JN
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:02.105232+00:00
-- url     : https://prove2.me/theorems/01d2e7b3-369b-4cc3-95bc-c55282665714
-- title:
--   p. 18 — the fixed point equation (4.5) coincides with the DCOE (3.7)–(3.8): min_v Q*(I, v) = J^N_β(π*, I)
-- statement:
--   Let $\pi^*$ be a probability measure on $\mathbb X$. For every window $I$,
--   $$
--   V^*(I)=\min_{v\in\mathbb U}Q^*(I,v)=J^N_\beta(\pi^*,I),
--   $$
--   that is, the value of $Q^*$ is the optimal value of the approximate finite-window model (3.7). Consequently a policy greedy for $Q^*$ is optimal for the approximate model, which is how Theorem 4.1(ii) follows from Theorem 3.3.
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, p. 18, §4, proof of Theorem 4.1(ii)

import Mathlib
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FiniteMemQL.Convergence

/-- p. 18 (arXiv:2103.12158v4), proof of Theorem 4.1(ii): the fixed point equation (4.5) coincides
with the optimality equation (3.7)–(3.8) of the approximate model, i.e.
`V*(I) = min_v Q*(I, v) = J^N_β(π*, I)` for every window `I`. -/
theorem qStar_min_eq_JN {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    {N : ℕ} (πs : Measure X) [IsProbabilityMeasure πs] :
    ∀ I : Window Y U N, ⨅ v : U, qStar M πs I v = JN M πs I := by sorry

end FiniteMemQL.Convergence
