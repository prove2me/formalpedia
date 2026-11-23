-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_5_10
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:12:29.77481+00:00
-- url     : https://prove2.me/theorems/ccabf07d-1498-497e-9bd8-7fd48d5e786b
-- title:
--   Theorem 5.10 — under Assumption 5.18 or 5.19 a stable $f\in\Pi_{SSD}$ is sample path average cost optimal in $\Pi_{SR}$
-- statement:
--   Under the standing assumptions of §5.3, suppose Assumption 5.18 (near monotonicity: $\liminf_{i\to\infty}\min_{a\in A}c(i,a)>\rho^*=\inf_{f\in\Pi_{SSR}}\int c\,d\hat\eta(f)$) or Assumption 5.19 (every $f\in\Pi_{SR}$ is stable and $I_R$ is compact). Then there is a stable $f\in\Pi_{SSD}$ that is sample path average cost optimal in $\Pi_{SR}$: for some constant $\rho^*\in[0,\infty]$,
--   $$\limsup_{N\to\infty}\frac1N\sum_{t<N}c(X_t,A_t)=\rho^*\quad\mathcal P^f_\mu\text{-a.s.},\qquad \limsup_{N\to\infty}\frac1N\sum_{t<N}c(X_t,A_t)\ge\rho^*\quad\mathcal P^{f'}_\mu\text{-a.s.}$$
--   for every initial law $\mu$ and every $f'\in\Pi_{SR}$.
--
--   **Formalization Note** Stability of $f$ is positive recurrence of its chain (the published `IsPositiveRecurrent`). The constant is in $[0,\infty]$ because $c\ge0$ and $J_s$ is extended real-valued (p. 287).
--
--   Differences from the source:
--   - reading: the standing assumptions of §5.3 (p. 309): U(i) replicas of one compact metric A, S the single communicating class under every f ∈ Π_SR → CMP with U(i) = A, A compact metric (with its automatic second countability as an instance), irreducibility under every stationary randomized policy; reason: these are the section's stated standing assumptions
--   - encoding: initial laws μ ∈ 𝒫(S) and 𝒫^π_μ → 𝒫^π_μ = ∑_i μ({i}) 𝒫^π_i for probability measures μ on ℕ; reason: on a countable state space the path law from μ is this mixture
--   - encoding: the constant ρ* of sample path optimality (p. 288) → ρ* ∈ [0, ∞], J_s in [0, ∞]; reason: c ≥ 0 and J_s is an extended real-valued random variable (p. 287); with unbounded costs every stable policy can have ∫ c dη̂(f) = ∞ (one action, i.i.d. jumps to j with probability 2^{−(j+1)}, c(i) = 2^i: Assumptions 5.19 and 5.20 hold and J_s = ∞ a.s.), so the constant may be +∞
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 312, Theorem 5.10, Assumptions 5.18–5.19; p. 288, sample path AC optimality

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Occupation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.VanishingDiscount

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 5.10 (p. 312), under the standing assumptions of §5.3. Under Assumption 5.18 or
Assumption 5.19 there is a stable `f ∈ Π_SSD` which is sample path average cost optimal in
`Π_SR`: for some finite `ρ*`, `J_s = ρ*` a.s. under `f` from every initial law, and `J_s ≥ ρ*`
a.s. under every `f' ∈ Π_SR` from every initial law. -/
theorem theorem_5_10 {A : Type*} [MetricSpace A] [CompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (hstd : StandingConvex M) (hA : Assumption518 M ∨ Assumption519 M) :
    ∃ g : StationaryPolicy M, IsPositiveRecurrent M g ∧
      IsSamplePathOptimalIn M {π | ∃ φ : RandRule M, π = φ.toPolicy} g.toPolicy := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
