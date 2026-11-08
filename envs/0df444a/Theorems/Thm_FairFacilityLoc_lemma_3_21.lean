-- Prove2me | Theorems.Thm_FairFacilityLoc_lemma_3_21
-- name    : FairFacilityLoc.lemma_3_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:33.035362+00:00
-- url     : https://prove2.me/theorems/52cbe372-f792-4bb9-bbf8-e9c6aebbf7ec
-- title:
--   Lemma 3.21 — monotonicity of $\bar h$, $\omega$ and concavity of $g$
-- statement:
--   Let $d\ge1$ be a real number and $b\in[0,1]$, and define $\bar h,\omega,g$ with $b$ in place of $b_d$, so that $\eta(t)=(1+b)t(1+t)$. Then $\bar h$ and $\omega$ are strictly increasing on $(0,1]$, and $g$ is concave on $[0,1/d]$.
--
--   These two properties let the shares of different coordinates be compared and averaged.
--
--   Differences from the source: none.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Lemma 3.21, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_FairFacilityLoc_hbar

namespace FairFacilityLoc

/-- **Lemma 3.21** (Yan, Zhou, manuscript, sha256 642a1268…, p.38, PDF p.40). For a real number `d ≥ 1` and `b ∈ [0, 1]`,
`h̄` and `ω` are strictly increasing on `(0, 1]`, and `g` is concave on `[0, 1/d]`. -/
theorem lemma_3_21 (d b : ℝ) (hd : 1 ≤ d) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    StrictMonoOn (hbar d b) (Set.Ioc 0 1) ∧
      StrictMonoOn (omegaFun d b) (Set.Ioc 0 1) ∧
      ConcaveOn ℝ (Set.Icc 0 (1 / d)) (gEnvelope d b) := by sorry

end FairFacilityLoc
