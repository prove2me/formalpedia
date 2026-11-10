-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_lemma_3_1
-- name    : DistRobustHalfspace.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:19:22.893217+00:00
-- url     : https://prove2.me/theorems/45a85a79-0a2b-481a-890c-8a38b253bf14
-- title:
--   Lemma 3.1 — concentration of the test statistic Z of Algorithm 1
-- statement:
--   Under the standing assumptions of §§2–3, with $m=\Theta(n^{2/3}/\varepsilon^{10})$ for a sufficiently large constant. Let $f:\mathbb R^n\to\{\pm1\}$ and $D$ a distribution on $\mathbb R^n$. Let $|\hat t|\le T_\varepsilon$ and let $N$ be a neighborhood tuple. Suppose:
--   1. either (a) $D=\mathcal N(0,I_n)$, $f$ is a halfspace and $\hat t$ is an $\varepsilon^4$-good threshold estimate for $f$, or (b) $D$ is $B$-typical with respect to $(f,\hat t)$;
--   2. $\|\mathbb E_{y\sim D}[yy^\top]\|_F\le2\sqrt n$;
--   3. $\|\mathbb E_{y\sim D}[f(y)\hat\alpha_{f,N}(y)y]\|_2^2\le4(\sqrt n+R_\varepsilon^2)$.
--
--   Then with probability at least $99/100$ over the draws of lines 7–10 of Algorithm 1, the statistic $Z$ satisfies both:
--   - if $\mathrm{DD}^{\hat t}_{\hat\alpha_{f,N}}(f,D)\le\varepsilon^3/128$ then $Z\le\varepsilon^3/64$;
--   - if $\mathrm{DD}^{\hat t}_{\hat\alpha_{f,N}}(f,D)>\varepsilon^3/32$ then $Z>\varepsilon^3/64$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §§2–3 (p. 11): n ≥ n₀, ε ≤ ε₀, ε ≥ 1/n for suitable absolute constants n₀, ε₀ → `∃ n₀ ε₀ > 0` quantified before f, D, t̂, N, with hypotheses `n₀ ≤ n`, `ε ≤ ε₀`, `1/n ≤ ε`; reason: the section's standing assumptions, stated as binders (FAITHFULNESS_TRAPS row 19)
--   - reading: m = Θ(n^{2/3}/ε^{10}) "with a sufficiently large constant" → `m = ⌈cm·n^{2/3}/ε^{10}⌉`, `∃ c₀, ∀ cm ≥ c₀, ∃ n₀ ε₀ …`; reason: a sufficiently large constant is any constant above a threshold; n₀, ε₀ are fixed after it
--   - encoding: "with probability at least 99/100, the Z from Algorithm 1" (t̂, N fixed) → `99/100 ≤ line7Law n m D {q | …}` for `statZ ε t̂ f N w z y`; reason: the probability is over the draws w, z, y of line 7 only
--   - encoding: a neighborhood tuple N → `N : Fin p → Rn n` with `0 < p`; reason: ℓ_{f,N} is undefined for p = 0
--   - reading: "f is a halfspace ... t̂ is a ξ-good threshold estimate for f" → `IsGoodThreshold f ξ t̂`: f = sgn(⟨x, v⟩ − t) with ‖v‖ = 1 and |t − t̂| ≤ ξ; reason: Definition 2.4 defines ξ-good only for unit-normal halfspaces, so the hypothesis already says f is one
--   - encoding: DD^{t̂}_β(f, D) = E_{y∼D}[(f(y)(⟨y, E[ṽ(t̂)]⟩ − t̂) − β(y))²] → `DD β t̂ f D : ℝ≥0∞`, a lower Lebesgue integral of the nonnegative integrand; reason: the expectation of a nonnegative function, +∞ when not integrable, never a junk 0
--   - encoding: Borel f : ℝⁿ → {±1} (footnote 1) → `f : Rn n → ℝ` with `IsBoolFn f` (measurable, values ±1); reason: real values make f(x)·x and f(y)(⟨y, v⟩ − t) direct; same functions
--   - encoding: Borel probability distribution D on ℝⁿ (footnote 1) → `D : ProbabilityMeasure (Rn n)`; reason: same objects
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Lemma 3.1, p. 25 (PDF 27)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
import Definitions.Def_DistRobustHalfspace_Main_Algorithm1
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Lemma 3.1 (p. 25): concentration of the statistic `Z` of Algorithm 1 (lines 7–10, with
`m = Θ(n^{2/3}/ε^{10})` for a sufficiently large constant, and `t̂`, `N` fixed). If (1) either
`D = N(0, Iₙ)` and `t̂` is an `ε⁴`-good threshold estimate for the halfspace `f`, or `D` is
`B`-typical w.r.t. `(f, t̂)`; (2) `‖E[y yᵀ]‖_F ≤ 2√n`; (3) `‖E[f(y) α̂_{f,N}(y) y]‖₂² ≤ 4(√n + R_ε²)`;
then with probability at least `99/100`: `DD ≤ ε³/128 ⇒ Z ≤ ε³/64` and `DD > ε³/32 ⇒ Z > ε³/64`. -/
theorem lemma_3_1 :
    ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∃ n₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → 1 / (n : ℝ) ≤ ε →
      ∀ (f : Rn n → ℝ), IsBoolFn f → ∀ (D : ProbabilityMeasure (Rn n)) (t' : ℝ),
        |t'| ≤ Teps ε → ∀ (p : ℕ) (N : Fin p → Rn n), 0 < p →
        ((D = gaussPM n ∧ IsGoodThreshold f (ε ^ 4) t') ∨
            IsTypicalDist ε f t' (D : Measure (Rn n))) →
        frobNorm (secondMoment (D : Measure (Rn n))) ≤ 2 * Real.sqrt n →
        ‖weightedCentroid ε f N (D : Measure (Rn n))‖ ^ 2 ≤ 4 * (Real.sqrt n + Reps ε ^ 2) →
        (99 / 100 : ℝ≥0∞) ≤ line7Law n (alg1M cm n ε) D
          {q | (DD (alphaHat ε f N) t' f (D : Measure (Rn n)) ≤ ENNReal.ofReal (ε ^ 3 / 128) →
                  statZ ε t' f N q.1 q.2.1 q.2.2 ≤ ε ^ 3 / 64) ∧
               (ENNReal.ofReal (ε ^ 3 / 32) < DD (alphaHat ε f N) t' f (D : Measure (Rn n)) →
                  ε ^ 3 / 64 < statZ ε t' f N q.1 q.2.1 q.2.2)} := by sorry

end DistRobustHalfspace.Main
