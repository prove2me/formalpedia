-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_5_11
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:12:59.7408+00:00
-- url     : https://prove2.me/theorems/fda8fa72-c2db-4af9-8dbf-030b1fe93760
-- title:
--   Theorem 5.11 — under Assumption 5.18 or 5.20 some $f\in\Pi_{SD}$ is sample path average cost optimal against all policies
-- statement:
--   Under the standing assumptions of §5.3, suppose Assumption 5.18 or Assumption 5.20 ($\sup_{\pi\in\Pi}E^\pi_0[\tau^2]<\infty$ with $\tau=\min\{t\ge1:X_t=0\}$). Then there is $f\in\Pi_{SD}$ that is sample path average cost optimal: for some constant $\rho^*\in[0,\infty]$, $J_s=\rho^*$ $\mathcal P^f_\mu$-a.s. for every initial law $\mu$, and $J_s\ge\rho^*$ $\mathcal P^\pi_\mu$-a.s. for every admissible $\pi\in\Pi$ and every initial law $\mu$, where $J_s=\limsup_N N^{-1}\sum_{t<N}c(X_t,A_t)$.
--
--   Unlike Theorem 5.10, the comparison is against all history-dependent randomized policies.
--
--   **Formalization Note** The printed theorem asserts $f\in\Pi_{SD}$ (the source map's summary says $\Pi_{SSD}$); the statement follows the printed page.
--
--   Differences from the source:
--   - reading: the standing assumptions of §5.3 (p. 309): U(i) replicas of one compact metric A, S the single communicating class under every f ∈ Π_SR → CMP with U(i) = A, A compact metric (with its automatic second countability as an instance), irreducibility under every stationary randomized policy; reason: these are the section's stated standing assumptions
--   - encoding: initial laws μ ∈ 𝒫(S) and 𝒫^π_μ → 𝒫^π_μ = ∑_i μ({i}) 𝒫^π_i for probability measures μ on ℕ; reason: on a countable state space the path law from μ is this mixture
--   - encoding: the constant ρ* of sample path optimality (p. 288) → ρ* ∈ [0, ∞], J_s in [0, ∞]; reason: c ≥ 0 and J_s is an extended real-valued random variable (p. 287); with unbounded costs every stable policy can have ∫ c dη̂(f) = ∞ (one action, i.i.d. jumps to j with probability 2^{−(j+1)}, c(i) = 2^i: Assumptions 5.19 and 5.20 hold and J_s = ∞ a.s.), so the constant may be +∞
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 313, Theorem 5.11, Assumption 5.20; p. 312, Assumption 5.18; p. 288, sample path AC optimality

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Occupation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.VanishingDiscount

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 5.11 (p. 313), under the standing assumptions of §5.3. Under Assumption 5.18 or
Assumption 5.20 there is an `f ∈ Π_SD` which is sample path average cost optimal: for some finite
`ρ*`, `J_s = ρ*` a.s. under `f` from every initial law, and `J_s ≥ ρ*` a.s. under every admissible
`π ∈ Π` from every initial law. -/
theorem theorem_5_11 {A : Type*} [MetricSpace A] [CompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (hstd : StandingConvex M) (hA : Assumption518 M ∨ Assumption520 M) :
    ∃ g : StationaryPolicy M, IsSamplePathOptimalIn M Set.univ g.toPolicy := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
