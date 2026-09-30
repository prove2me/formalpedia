-- Prove2me | Theorems.Thm_AllocationIndices_optimal_stopping_set
-- name    : AllocationIndices.optimal_stopping_set
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:27:58.462016+00:00
-- url     : https://prove2.me/theorems/bf11615d-0d24-4903-9996-c6328a22367f
-- title:
--   Lemma 2.2: the supremum in (2.6) is attained by the stopping rule with any stopping set Σ₀ between {ν(x) < ν(ξ)} and {ν(x) ≤ ν(ξ)}
-- statement:
--   **Lemma 2.2.** The supremum in (2.6) is attained by a stopping time $\tau$. For $x(0) = \xi$, this stopping time has a stopping set, say $\Sigma_0 \subseteq E$, which may be chosen to be any set such that
--   $$\{x : \nu(B, x) < \nu(B, \xi)\} \subseteq \Sigma_0 \subseteq \{x : \nu(B, x) \le \nu(B, \xi)\}.$$
--
--   Formally: for a bandit process on a countable state space with bounded reward and $a \in (0,1)$, every state $\xi$ and every set $\Sigma_0$ of states with the two inclusions above, the stopping rule "stop at the first decision time $t \ge 1$ at which $x(t) \in \Sigma_0$" is a positive stopping time $\tau$, and $\nu_\tau(B, \xi) = R_\tau(B, \xi)/W_\tau(B, \xi) = \nu(B, \xi)$. Taking $\Sigma_0 = \{x : \nu(B, x) < \nu(B, \xi)\}$ gives the attainment claim. In a countable state space every set is measurable, so no measurability condition on $\Sigma_0$ is needed.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §2.6.3 p. 30, Lemma 2.2, with its proof on p. 31

import Definitions.Def_AllocationIndices_Index

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem optimal_stopping_set {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ξ : S) (stopSet : Set S)
    (h₁ : {x | gittinsIndex P r a x < gittinsIndex P r a ξ} ⊆ stopSet)
    (h₂ : stopSet ⊆ {x | gittinsIndex P r a x ≤ gittinsIndex P r a ξ}) :
    IsPositiveStoppingTime (hittingTime stopSet) ∧
      stoppedRatio P r a (hittingTime stopSet) ξ = gittinsIndex P r a ξ := by sorry

end AllocationIndices
