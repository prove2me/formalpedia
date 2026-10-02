-- Prove2me | Theorems.Thm_AllocationIndices_favourable_index_eq_cps
-- name    : AllocationIndices.favourable_index_eq_cps
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:02:41.194986+00:00
-- url     : https://prove2.me/theorems/71ab1879-9567-4981-b60f-ea4a087a3a7e
-- title:
--   Proposition 7.4: for a target process in a favourable state, the Gittins index equals the current probability of success
-- statement:
--   **Proposition 7.4.** If $S$ is a target process and the probability density $\pi$ for the parameter $\theta$ is favourable, then $\nu(S, \pi) = r(S, \pi)$.
--
--   Formally: for a conjugate sampling model, a target $T$, a state $p$ that is favourable for $T$ (along every finite sequence of observations below $T$ the current probability of success never exceeds its value at $p$) and $a \in (0, 1)$, the Gittins index of the target process in the state $p$ equals its current probability of success $f([T, \infty) \mid p)$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.3 p. 181, Proposition 7.4 (from Proposition 2.7)

import Definitions.Def_AllocationIndices_Sampling

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

/-- **Proposition 7.4** (p. 181). If `S` is a target process and the probability density `π` for
the parameter `θ` is favourable, then `ν(S, π) = r(S, π)`: the Gittins index of the target
process in a favourable state equals its current probability of success. -/
theorem favourable_index_eq_cps {Θ P : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [Nonempty Θ] [MeasurableSpace P] (F : SamplingModel Θ P) (hconj : F.IsConjugate) (T : ℝ)
    (p : P) (hfav : F.IsFavourable T p) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    gittinsIndex (F.targetChain T) (F.targetReward T) a (Sum.inl p) =
      F.targetReward T (Sum.inl p) := by sorry

end AllocationIndices
