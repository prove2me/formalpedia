-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_lemma_5_1
-- name    : ArapostathisAC.VanishingDiscount.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:11:22.73881+00:00
-- url     : https://prove2.me/theorems/2f5d305b-ed43-423d-9e20-ad087e3875dc
-- title:
--   Lemma 5.1 — almost surely, every limit point $\nu$ of the empirical measures with $\delta_\nu>0$ has $\nu'=\hat\eta(f)$ for a stable $f\in\Pi_{SSR}$
-- statement:
--   Under the standing assumptions of §5.3, let $\pi\in\Pi$ and let $\mu$ be an initial law on $S$. Let $\nu_t=t^{-1}\sum_{s<t}\delta_{(X_s,A_s)}$ be the empirical measures (5.17), viewed in $\mathcal P(\bar S\times A)$ with $\bar S=S\cup\{\infty\}$, and decompose a $\nu\in\mathcal P(\bar S\times A)$ as in (5.18), $\nu=\delta_\nu\nu'+(1-\delta_\nu)\nu''$ with $\delta_\nu=\nu(S\times A)$. Outside a $\mathcal P^\pi_\mu$-null set: for every limit point $\nu$ of $\{\nu_t\}$ with $\delta_\nu>0$,
--   $$\nu'=\hat\eta(f)\qquad\text{for some }f\in\Pi_{SSR},$$
--   that is, $\nu(B)=\delta_\nu\,\hat\eta(f)(B)$ for every Borel $B\subseteq S\times A$.
--
--   The lemma identifies the non-escaping part of the empirical occupation measures with ergodic occupation measures of stable policies; it is the step that lets the convex analytic approach compare arbitrary policies with stationary ones.
--
--   **Formalization Note** $\bar S$ is $\mathbb N_\infty$, which is the one-point compactification of $\mathbb N$; $\nu_t$ is indexed from $t=1$. Limit points are cluster points in the weak topology.
--
--   Differences from the source:
--   - reading: the standing assumptions of §5.3 (p. 309): U(i) replicas of one compact metric A, S the single communicating class under every f ∈ Π_SR → CMP with U(i) = A, A compact metric (with its automatic second countability as an instance), irreducibility under every stationary randomized policy; reason: these are the section's stated standing assumptions
--   - encoding: initial laws μ ∈ 𝒫(S) and 𝒫^π_μ → 𝒫^π_μ = ∑_i μ({i}) 𝒫^π_i for probability measures μ on ℕ; reason: on a countable state space the path law from μ is this mixture
--   - encoding: η̂(f) for f ∈ Π_SSR → occ f η built from an invariant probability vector η of f; reason: under the standing irreducibility the invariant probability vector of a stable f is unique
--   - encoding: ν′ = η̂(f) with ν′ from the decomposition (5.18) → ν(B) = δ_ν η̂(f)(B) for every Borel B ⊆ S × A (B identified with its image in S̄ × A); reason: for δ_ν > 0 this is the definition of ν′
--   - encoding: the one-point compactification S̄ of S → ℕ∞ with its order topology and discrete σ-algebra; reason: ℕ∞ is homeomorphic to the one-point compactification of ℕ, and its Borel σ-algebra is discrete
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 310, Lemma 5.1, (5.18); p. 309, (5.17) and §5.3 setting

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Occupation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.VanishingDiscount

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Lemma 5.1 (p. 310), under the standing assumptions of §5.3. Let `π ∈ Π` and let `μ` be an
initial law. Outside a `𝒫^π_μ`-null set: for every limit point `ν` in `𝒫(S̄ × A)` of the empirical
measures `ν_t` (5.17) with `δ_ν = ν(S × A) > 0`, the normalized restriction `ν'` of `ν` to `S × A`
in (5.18) equals `η̂(f)` for some `f ∈ Π_SSR`; that is, `ν(B) = δ_ν η̂(f)(B)` for every Borel
`B ⊆ S × A`. -/
theorem lemma_5_1 {A : Type*} [MetricSpace A] [CompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (hstd : StandingConvex M) (π : Policy M) (μ : Measure ℕ)
    [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂(pathLawC M π μ), ∀ ν : ProbabilityMeasure (ℕ∞ × A),
      MapClusterPt ν atTop (empiricalP ω) →
      0 < (ν : Measure (ℕ∞ × A)) (Set.range embedS) →
      ∃ φ : RandRule M, IsStableR M φ ∧ ∃ η, IsInvariantProb M φ η ∧
        ∀ B : Set (ℕ × A), MeasurableSet B →
          (ν : Measure (ℕ∞ × A)) (embedS '' B) =
            (ν : Measure (ℕ∞ × A)) (Set.range embedS) * occ φ η B := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
