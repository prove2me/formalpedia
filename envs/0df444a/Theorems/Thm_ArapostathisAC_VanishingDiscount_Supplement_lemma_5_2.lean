-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_lemma_5_2
-- name    : ArapostathisAC.VanishingDiscount.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:11:57.266614+00:00
-- url     : https://prove2.me/theorems/d198d45e-ab34-470a-89e5-dad60e2ec32e
-- title:
--   Lemma 5.2 — $I_R$ and $I_D$ are closed, and $I_R$ is convex with its extreme points in $I_D$
-- statement:
--   Under the standing assumptions of §5.3, let $I_R=\{\hat\eta(f):f\in\Pi_{SSR}\}$ and $I_D=\{\hat\eta(f):f\in\Pi_{SSD}\}$ be the sets of ergodic occupation measures of stable stationary randomized and deterministic policies. Then $I_R$ and $I_D$ are closed in $\mathcal P(S\times A)$ (weak topology); $I_R$ is convex; and every extreme point of $I_R$ lies in $I_D$.
--
--   Together with Choquet's theorem this reduces the minimization of $\nu\mapsto\int c\,d\nu$ over $I_R$ to stationary deterministic policies.
--
--   **Formalization Note** Convex combinations and extreme points use scalars in $[0,\infty]$ with $a+b=1$, which forces $a,b\in[0,1]$, so they are the usual ones.
--
--   Differences from the source:
--   - reading: the standing assumptions of §5.3 (p. 309): U(i) replicas of one compact metric A, S the single communicating class under every f ∈ Π_SR → CMP with U(i) = A, A compact metric (with its automatic second countability as an instance), irreducibility under every stationary randomized policy; reason: these are the section's stated standing assumptions
--   - encoding: η̂(f) for f ∈ Π_SSR → occ f η built from an invariant probability vector η of f; reason: under the standing irreducibility the invariant probability vector of a stable f is unique
--   - encoding: convexity and extreme points in the space of finite measures with real scalars → Convex and extremePoints over the scalars [0, ∞] in the cone of measures; reason: a + b = 1 forces a, b ∈ [0, 1]; the convex combinations are the same
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 311, Lemma 5.2; p. 309, definitions of I_R and I_D

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Occupation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.VanishingDiscount

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Lemma 5.2 (p. 311), under the standing assumptions of §5.3. The sets `I_R` and `I_D` are
closed in `𝒫(S × A)` (weak topology); also, `I_R` is convex and has its extreme points in `I_D`. -/
theorem lemma_5_2 {A : Type*} [MetricSpace A] [CompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (hstd : StandingConvex M) :
    IsClosed {μ : ProbabilityMeasure (ℕ × A) | (μ : Measure (ℕ × A)) ∈ occR M} ∧
    IsClosed {μ : ProbabilityMeasure (ℕ × A) | (μ : Measure (ℕ × A)) ∈ occD M} ∧
    Convex ℝ≥0∞ (occR M) ∧ Set.extremePoints ℝ≥0∞ (occR M) ⊆ occD M := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
