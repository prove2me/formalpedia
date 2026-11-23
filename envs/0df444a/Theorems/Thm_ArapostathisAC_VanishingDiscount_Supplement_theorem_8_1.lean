-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_8_1
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:16:24.078977+00:00
-- url     : https://prove2.me/theorems/3ce32bfe-0ff9-448b-81d3-50e9d071cd27
-- title:
--   Theorem 8.1 — every extreme point of $H=I_R\cap\{\psi:\int g\,d\psi\le a\}$ is $\hat\eta(f)$ with $f$ randomizing at most at one state between two actions
-- statement:
--   In the constrained model of §8 ($S=\{0,1,2,\dots\}$, common compact metric action space $A=U(i)$, $P(j\mid i,a)$ continuous in $a$, irreducibility under every $f\in\Pi_{SR}$ as in §5.3, and Assumption 5.20), let $g\in C_b(S\times A)$, $a\in\mathbb R$, and
--   $$H=I_R\cap\Big\{\psi:\int g\,d\psi\le a\Big\},$$
--   assumed nonempty. Then every extreme point of $H$ is $\hat\eta(f)$ for a stable $f\in\Pi_{SR}$ such that $f(i)$ is a Dirac measure for all but at most one $i$, and at the remaining $i$, if any, $f(i)$ is a convex combination of two Dirac measures.
--
--   This is the structural fact behind the classical result that a constrained average cost problem with one constraint has an optimal policy that randomizes at one state only.
--
--   **Formalization Note** Extreme points use scalars in $[0,\infty]$ with $a+b=1$; the remaining state $i_0$ is arbitrary when there is none.
--
--   Differences from the source:
--   - reading: the standing assumptions of §5.3 (p. 309): U(i) replicas of one compact metric A, S the single communicating class under every f ∈ Π_SR → CMP with U(i) = A, A compact metric (with its automatic second countability as an instance), irreducibility under every stationary randomized policy; reason: these are the section's stated standing assumptions
--   - encoding: η̂(f) for f ∈ Π_SSR → occ f η built from an invariant probability vector η of f; reason: under the standing irreducibility the invariant probability vector of a stable f is unique
--   - reading: f ∈ Π_SR with η̂(f) its occupation measure → f stable (f ∈ Π_SSR); reason: η̂(f) is defined only for stable f (p. 309)
--   - encoding: a convex combination of two Dirac measures → t δ_{b₁} + (1 − t) δ_{b₂} with t ∈ [0, 1]; reason: the same set of measures
--   - encoding: extreme points of the convex set H → extremePoints over the scalars [0, ∞]; reason: a + b = 1 forces a, b ∈ [0, 1]
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 334, Theorem 8.1; p. 333, §8 setting, (8.1), definition of H and Assumption 5.20

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Occupation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.VanishingDiscount

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 8.1 (p. 334), in the constrained model of §8 (`S = ℕ`, common compact metric `A`,
`U(i) = A`, irreducibility under every `f ∈ Π_SR`, Assumption 5.20). Let `g ∈ C_b(S × A)`,
`a ∈ ℝ`, and `H = I_R ∩ {ψ : ∫ g dψ ≤ a}`, assumed nonempty. Each extreme point of `H` is
`η̂(f)` for some `f ∈ Π_SR` such that `f(i)` is a Dirac measure for all but at most one `i`, and
at the remaining `i`, if any, `f(i)` is a convex combination of two Dirac measures. -/
theorem theorem_8_1 {A : Type*} [MetricSpace A] [CompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (hstd : StandingConvex M) (h520 : Assumption520 M)
    (g : ℕ × A → ℝ) (hg : Continuous g) (hgb : ∃ C, ∀ p, |g p| ≤ C) (a : ℝ)
    (hH : (occR M ∩ {ψ | ∫ p, g p ∂ψ ≤ a}).Nonempty) :
    ∀ μ ∈ Set.extremePoints ℝ≥0∞ (occR M ∩ {ψ | ∫ p, g p ∂ψ ≤ a}),
      ∃ φ : RandRule M, IsStableR M φ ∧ ∃ η, IsInvariantProb M φ η ∧ μ = occ φ η ∧
        ∃ i₀ : ℕ, (∀ i, i ≠ i₀ → ∃ b : A, φ.rule i = Measure.dirac b) ∧
          ∃ (b₁ b₂ : A) (t : ℝ≥0∞), t ≤ 1 ∧
            φ.rule i₀ = t • Measure.dirac b₁ + (1 - t) • Measure.dirac b₂ := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
