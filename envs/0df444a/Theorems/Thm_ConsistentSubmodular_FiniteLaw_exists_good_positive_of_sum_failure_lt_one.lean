-- Prove2me | Theorems.Thm_ConsistentSubmodular_FiniteLaw_exists_good_positive_of_sum_failure_lt_one
-- name    : ConsistentSubmodular.FiniteLaw.exists_good_positive_of_sum_failure_lt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:30.610966+00:00
-- url     : https://prove2.me/theorems/1607b1d9-57a6-4704-9e10-cfafdd5836b0
-- title:
--   Union bound — some positive-weight outcome avoids all bad events
-- statement:
--   Let $\mu$ be a probability law on a finite set $\Omega$ (nonnegative weights $\mu(\omega)$ summing to $1$), let $\kappa$ be a finite index type, and for each $i\in\kappa$ let $\mathrm{bad}_i\subseteq\Omega$ be an event. If
--   $$\sum_{i\in\kappa}\mu(\mathrm{bad}_i)<1,$$
--   then there is an outcome $\omega\in\Omega$ with $\mu(\omega)>0$ such that $\omega\notin \mathrm{bad}_i$ for every $i\in\kappa$.
--
--   This is the finite union-bound form of the probabilistic method: it turns a bound on the total failure probability of finitely many events into the existence of a good outcome of positive weight. It is used in the rounding and sampling steps of the deterministic reduction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/FiniteProbability.lean#L68-L85 (`ConsistentSubmodular.FiniteLaw.exists_good_positive_of_sum_failure_lt_one`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProbability

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem ConsistentSubmodular.FiniteLaw.exists_good_positive_of_sum_failure_lt_one {κ : Type*} [Fintype κ]
    (bad : κ → Ω → Prop) (hbad : (∑ i, μ.probability (bad i)) < 1) :
    ∃ ω, 0 < μ.weight ω ∧ ∀ i, ¬bad i ω := by sorry
