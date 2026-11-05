-- Prove2me | Theorems.Thm_CalendarDependentRM_theorem_3_1
-- name    : CalendarDependentRM.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:07.082849+00:00
-- url     : https://prove2.me/theorems/63037581-90c1-41c8-8553-7a00e9d77d55
-- title:
--   Theorem 3.1 (Upper Bound): $\overline Z_{LP}\ge\mathrm{OPT}$
-- statement:
--   The fluid approximation (2) has an optimal solution, and its optimal objective value $\overline Z_{LP}$ is an upper bound on the optimal total expected revenue:
--
--   $$
--   \overline Z_{LP}\ge\mathrm{OPT}.
--   $$
--
--   This makes the fluid approximation usable as a benchmark for any policy, and it is the comparison used by the performance guarantee.
--
--   Differences from the source:
--   - generalization: the standing transition assumption → no assumption on the demand process; reason: the optimal policy gives a feasible solution of (2) with objective OPT for any Markov demand; the source case is an instance
--   - encoding: $\overline Z_{LP}$ is the optimal objective value of problem (2) → `objective x` at an optimal `x`, with the existence of an optimum as a clause; reason: avoids a junk value from `sSup`; the feasible set is compact and nonempty
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - encoding: conditional probabilities given a null event are undefined → they read $0$ (a ratio with $0/0=0$), or the zero measure for `cond`; reason: this only concerns states the policy never reaches, and such states have zero objective coefficient
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Theorem 3.1, p.10

import Mathlib
import Definitions.Def_CalendarDependentRM_Instance

namespace CalendarDependentRM

/-- **Theorem 3.1 (Upper Bound).** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Theorem 3.1, p. 10 (proof
Extended Results pp. 7–8): the optimal objective value `Z_LP` of problem (2) satisfies `Z_LP ≥ OPT`.

Problem (2) has an optimal solution, and `OPT ≤ objective x` at every optimal solution `x`.

**Formalization Note** `Z_LP` is `I.objective x` at an optimal `x`, whose existence is a clause, not `sSup`. No
transition assumption is needed. -/
theorem theorem_3_1 {R J : Type*} [Fintype J] {K T : ℕ} (I : Instance R J K T) :
    (∃ x, I.IsOptimal x) ∧ ∀ x, I.IsOptimal x → I.OPT ≤ I.objective x := by sorry

end CalendarDependentRM
