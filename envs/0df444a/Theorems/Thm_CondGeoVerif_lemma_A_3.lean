-- Prove2me | Theorems.Thm_CondGeoVerif_lemma_A_3
-- name    : CondGeoVerif.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:21:09.089585+00:00
-- url     : https://prove2.me/theorems/101562ec-e5dd-452a-828f-b9f0267afdb3
-- title:
--   Lemma A.3 — dimension-independent disagreement modulus $\omega_f$
-- statement:
--   Let $f:\mathbb R^k\to\{-1,1\}$ be Borel. There is a nondecreasing $\omega_f:[0,\infty)\to[0,1]$ with $\omega_f(s)\to0$ as $s\downarrow0$ such that, in every ambient dimension $d$, orthonormal $k$-frames $W,W'\in\mathbb R^{d\times k}$ satisfy
--   $$\mathbb P\{f(W^\top X)\ne f(W'^\top X)\}\le\omega_f(\|W-W'\|_F),\qquad X\sim N(0,I_d).$$
--   Consequently a Euclidean $\rho$-net of a set of orthonormal frames is a prediction-disagreement $\omega_f(\rho)$-net.
--
--   No continuity of $f$ is required; this lets protocols discretize frames for an arbitrary Borel rule.
--
--   Differences from the source:
--   - generalization: a Euclidean ρ-net of any compact set of orthonormal coefficient frames → any set of orthonormal frames and any ρ-net of it consisting of orthonormal frames; reason: compactness is not used; compact sets are a special case
--   - encoding: ω_f : [0, ∞) → [0, 1] → ω : ℝ → ℝ, monotone with values in [0, 1] on [0, ∞); reason: values on negative arguments are never used
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Lemma A.3, p.15 (PDF p.18)

import Mathlib
import Definitions.Def_CondGeoVerif_projClass

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel

namespace CondGeoVerif

/-- **Lemma A.3 (Dimension-independent disagreement modulus)** (Chen, *The Conditional Geometry of
Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, p.15 = PDF p.18). For a
Borel rule `f : ℝᵏ → {−1, 1}` there is a nondecreasing `ω_f : [0, ∞) → [0, 1]` with
`ω_f(s) → 0` as `s ↓ 0` such that, in every ambient dimension `d`, orthonormal `k`-frames `W, W'`
satisfy `P{f(WᵀX) ≠ f(W'ᵀX)} ≤ ω_f(‖W − W'‖_F)`, `X ∼ N(0, I_d)`. Consequently a Euclidean
`ρ`-net of a set of orthonormal frames is a prediction-disagreement `ω_f(ρ)`-net.

**Formalization Note** `ω_f` is chosen before `d`. The net clause is stated for every set of
orthonormal frames and every net of orthonormal frames, compact or not. -/
theorem lemma_A_3 {k : ℕ} (f : Vec k → Bool) (hf : Measurable f) :
    ∃ ω : ℝ → ℝ, MonotoneOn ω (Set.Ici 0) ∧ (∀ s : ℝ, 0 ≤ s → 0 ≤ ω s ∧ ω s ≤ 1) ∧
      Filter.Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      (∀ d : ℕ, ∀ W ∈ stiefel d k, ∀ W' ∈ stiefel d k,
        (gauss d {x | frameRule f W x ≠ frameRule f W' x}).toReal ≤ ω (frob (W - W'))) ∧
      (∀ d : ℕ, ∀ S Net : Set (Matrix (Fin d) (Fin k) ℝ), S ⊆ stiefel d k → Net ⊆ stiefel d k →
        ∀ ρ : ℝ, 0 ≤ ρ → (∀ W ∈ S, ∃ W' ∈ Net, frob (W - W') ≤ ρ) →
          ∀ W ∈ S, ∃ W' ∈ Net,
            (gauss d {x | frameRule f W x ≠ frameRule f W' x}).toReal ≤ ω ρ) := by sorry

end CondGeoVerif
