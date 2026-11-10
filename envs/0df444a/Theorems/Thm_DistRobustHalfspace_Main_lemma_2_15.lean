-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_lemma_2_15
-- name    : DistRobustHalfspace.Main.lemma_2_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:18:18.61437+00:00
-- url     : https://prove2.me/theorems/e702b2e7-123b-4bc1-ab60-493bef48d8a8
-- title:
--   Lemma 2.15 — testing the YES case versus far-from-whittled with O(m) queries and samples
-- statement:
--   Under the standing assumptions of §§2–3. Let $K>0$ be any constant. There is an algorithm which, given query access to $f$, sample access to $D$, and parameters $\hat t\in\mathbb R$, $m\in\mathbb N$ with $|\hat t|\le T_\varepsilon$ and $\sqrt n\log n/\varepsilon^2\le m\le(n/\varepsilon)^{10}$, uses $O(m)$ queries and $O(m)$ samples. It accepts or rejects so that, with probability at least $99/100$, both hold:
--   1. if $f$ is a halfspace, $D$ is the standard Gaussian and $\hat t$ is an $\varepsilon^4$-good threshold estimate for $f$, it accepts;
--   2. if $\operatorname{dist}_{TV}(D,D^{\hat t}_*)>1/(Km)$, it rejects.
--
--   Here $D^{\hat t}_*$ is the whittled distribution (Definition 2.14) and $\operatorname{dist}_{TV}(P,Q)=\sup_A|P(A)-Q(A)|$ over Borel sets $A$ (the published `FoundationsRL.DECLower.tvDist`).
--
--   Differences from the source:
--   - encoding: standing assumptions of §§2–3 (p. 11): n ≥ n₀, ε ≤ ε₀, ε ≥ 1/n for suitable absolute constants n₀, ε₀ → `∃ n₀ ε₀ > 0` quantified before the tester family and its inputs, with hypotheses `n₀ ≤ n`, `ε ≤ ε₀`, `1/n ≤ ε`; reason: the section's standing assumptions, stated as binders (FAITHFULNESS_TRAPS row 19)
--   - reading: "Let K > 0 be any constant" with O(m) and absolute n₀, ε₀ → `∀ K > 0, ∃ C n₀ ε₀` (the O(m) constant and n₀, ε₀ may depend on K); reason: K is a constant of the lemma; the proof's union bound needs n large in terms of K
--   - generalization: "there is an algorithm" → there is a non-adaptive `Tester` (query points fixed by samples and internal randomness); reason: a non-adaptive algorithm is an algorithm, so the Lean statement implies the source's; the algorithm in the paper's proof is non-adaptive
--   - encoding: randomized algorithm with sample access to D and query access to f → `Tester`: i.i.d. samples from D, an internal seed on an arbitrary probability space, query points a function of samples and seed, output a function of samples, seed and answers, worst-case counts; jointly measurable (`IsMeasurable`); reason: the paper's model of a tester; measurability makes the output probabilities those of events
--   - encoding: an algorithm given parameters t̂ and m → a family `A t̂ m : Tester n Bool` chosen after n and ε, before D and f; reason: the algorithm may use its parameters but not D or f
--   - reading: "f is a halfspace ... t̂ is a ξ-good threshold estimate for f" → `IsGoodThreshold f ξ t̂`: f = sgn(⟨x, v⟩ − t) with ‖v‖ = 1 and |t − t̂| ≤ ξ; reason: Definition 2.4 defines ξ-good only for unit-normal halfspaces, so the hypothesis already says f is one
--   - encoding: "with probability at least p" → `p ≤ T.prob D f E` in `ℝ≥0∞` (product of D^{⊗samples} and the seed's law); reason: probabilities of events of a measurable tester
--   - encoding: Borel f : ℝⁿ → {±1} (footnote 1) → `f : Rn n → ℝ` with `IsBoolFn f` (measurable, values ±1); reason: real values make f(x)·x and f(y)(⟨y, v⟩ − t) direct; same functions
--   - encoding: Borel probability distribution D on ℝⁿ (footnote 1) → `D : ProbabilityMeasure (Rn n)`; reason: same objects
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Lemma 2.15, p. 17–18 (PDF 19–20)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
import Definitions.Def_FoundationsRL_DECLower_tvDist
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Lemma 2.15 (pp. 17–18): for every constant `K > 0` there is a tester which, given `t̂` with
`|t̂| ≤ T_ε` and `m` with `√n log n / ε² ≤ m ≤ (n/ε)^{10}`, uses `O(m)` queries and samples and
with probability at least `99/100`: accepts if `f` is a halfspace, `D = N(0, Iₙ)` and `t̂` is an
`ε⁴`-good threshold estimate for `f`; rejects if `dist_TV(D, D^{t̂}_∗) > 1/(Km)`. -/
theorem lemma_2_15 :
    ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → 1 / (n : ℝ) ≤ ε →
      ∃ A : ℝ → ℕ → Tester n Bool, ∀ (t' : ℝ) (m : ℕ), |t'| ≤ Teps ε →
        Real.sqrt n * Real.log n / ε ^ 2 ≤ m → (m : ℝ) ≤ ((n : ℝ) / ε) ^ 10 →
        (A t' m).IsMeasurable ∧ ((A t' m).numSamples : ℝ) ≤ C * m ∧
        ((A t' m).numQueries : ℝ) ≤ C * m ∧
        ∀ (D : ProbabilityMeasure (Rn n)) (f : Rn n → ℝ), IsBoolFn f →
          (99 / 100 : ℝ≥0∞) ≤ (A t' m).prob D f (fun o =>
            (IsGoodThreshold f (ε ^ 4) t' ∧ D = gaussPM n → o = true) ∧
            (1 / (K * m) < FoundationsRL.DECLower.tvDist (D : Measure (Rn n))
                (whittled ε f t' (D : Measure (Rn n))) → o = false)) := by sorry

end DistRobustHalfspace.Main
