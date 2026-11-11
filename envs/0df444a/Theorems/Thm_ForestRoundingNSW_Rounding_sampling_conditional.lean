-- Prove2me | Theorems.Thm_ForestRoundingNSW_Rounding_sampling_conditional
-- name    : ForestRoundingNSW.Rounding.sampling_conditional
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:51:08.269948+00:00
-- url     : https://prove2.me/theorems/6e9d0cfc-d787-4949-b341-21f5dd3cc8da
-- title:
--   §3.3, Sampling conditional on one item — z_p is the inclusion probability; the reweighted runs give the conditional laws
-- statement:
--   Let $f:2^G\to\mathbb R_{\ge0}$ be normalized, monotone and submodular, fix a choice rule, let $z\in[0,1]^G$ be the current vector of Algorithm 1, let $S$ be the final bundle of an unconditioned run from $z$, and fix an item $p$.
--
--   (i) The current coordinate is the probability of eventual inclusion: $\Pr[p\in S]=z_p$.
--
--   (ii) If $z_p>0$, running Algorithm 1 from $z$ with every transition $z'\to w$ of original probability $q$ reweighted to $q\,w_p/z'_p$ yields exactly the conditional law: for every $T\subseteq G$,
--   $$\Pr_{\text{incl}}[S=T]=\frac{\Pr[S=T]\,\mathbf 1[p\in T]}{z_p}.$$
--   If $z_p<1$, the reweighting $q\,(1-w_p)/(1-z'_p)$ yields $\Pr_{\text{excl}}[S=T]=\Pr[S=T]\,\mathbf 1[p\notin T]/(1-z_p)$.
--
--   This is the conditional-sampling step that Algorithm 2 uses for an agent's parent item.
--
--   Differences from the source:
--   - reading: Pr[p ∈ S | past choices] = z_p for the current vector z → for every start state z ∈ [0,1]^G, the run of Algorithm 1 from z includes p with probability z_p; reason: Algorithm 1 is a Markov chain on its state, so the run after the past choices is the run from the current vector
--   - reading: an item p whose desired conditioning event has positive probability → z_p > 0 for inclusion, z_p < 1 for exclusion; reason: by (i) these are exactly the positive-probability cases
--   - reading: an unconditioned run of Algorithm 1 → the function f is normalized monotone submodular and the same choice rule is used in both runs; reason: the context of Algorithm 1 (Lemma 3.2) and of Algorithm 2 line 7
--   - encoding: the reweighted probability of the second endpoint → the complement of the reweighted probability of the first endpoint; reason: on every state these runs reach the two reweighted probabilities add up to 1
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 24, §3.3, Sampling conditional on one item

import Mathlib
import Definitions.Def_ForestRoundingNSW_Rounding_SetFunctions
import Definitions.Def_ForestRoundingNSW_Rounding_BalancedRounding

namespace ForestRoundingNSW.Rounding

theorem sampling_conditional {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : IsNMS f) (ρ : (X → ℝ) → X × X) (hρ : IsChoiceRule ρ) (z : X → ℝ)
    (hz : InUnitCube z) (p : X) :
    prob (alg1Law f ρ z) (fun S => p ∈ S) = z p ∧
    (0 < z p → ∀ S : Finset X,
      (condLaw f ρ z p true S).toReal =
        (alg1Law f ρ z S).toReal * (if p ∈ S then 1 else 0) / z p) ∧
    (z p < 1 → ∀ S : Finset X,
      (condLaw f ρ z p false S).toReal =
        (alg1Law f ρ z S).toReal * (if p ∈ S then 0 else 1) / (1 - z p)) := by sorry

end ForestRoundingNSW.Rounding
