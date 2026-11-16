-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_Supplement_claim_7_7
-- name    : DetTerminalEmbedding1373.Real.Supplement.claim_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:17:07.093807+00:00
-- url     : https://prove2.me/theorems/b866f7cd-5a6b-4cbf-b152-a1e105bc6962
-- title:
--   Claim 7.7 — the rounded projection is within $\xi$ of the unit-ball projection
-- statement:
--   Let $0<\eta\le 1/2$ and $\xi=\eta^2/1024$. Let $v\in\mathbb Q^m$, let $r_v$ be an admissible radius for $v$ with accuracy $\xi$ (that is, $r_v=1$ if $R_v=\sum_j v_j^2\le 1$, and $\sqrt{R_v}\le r_v\le(1+\xi/4)\sqrt{R_v}$ otherwise), and let $N$ be an integer with $\sqrt m\,2^{-N}\le\xi/4$. Let $\Pi(v)$ be the rounded projection of equation (64) built from $r_v$ and $N$, and let $\operatorname{proj}(v)$ be the Euclidean projection of $v$ onto the closed unit ball $B_2^m=\{z\in\mathbb R^m:\|z\|\le 1\}$. Then
--
--   $$\|\Pi(v)-\operatorname{proj}(v)\|\le\xi.$$
--
--   This is the per-iteration error of the finite-precision projected subgradient method (Lemma 7.8): each exact projection step may be replaced by the rational vector $\Pi(v)$ at cost at most $\xi$.
--
--   Differences from the source:
--   - generalization: η = ε/12 for the rational accuracy ε ∈ (0, 1/2] of §7 → every real η with 0 < η ≤ 1/2; reason: η = ε/12 is such a real number, so the statement specializes to the source's
--   - reading: r_v and N are the values the algorithm computes → the conclusion holds for every admissible rational r_v and every integer N with √m·2^{-N} ≤ ξ/4; reason: the paper leaves the choice to the algorithm and its proof uses only these properties
--   - encoding: Π(v), proj(v) ∈ ℝ^m → rational vectors cast coordinatewise into EuclideanSpace ℝ (Fin m), proj = the published CalamaiMore.Convergence.proj onto the closed unit ball; reason: the nearest point of the closed unit ball exists and is unique, so the published projection is the exact one
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), p. 29, Claim 7.7 with equation (64) and the paragraph before it; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Mathlib
import Definitions.Def_DetTerminalEmbedding1373_Real_Supplement_roundedProjection
import Definitions.Def_CalamaiMore_Convergence_proj

set_option autoImplicit false

namespace DetTerminalEmbedding1373.Real.Supplement

/-- Claim 7.7, p. 29. With `ξ = η²/1024`, for every rational `v ∈ ℚᵐ`, every admissible radius
`r_v` and every integer `N` with `√m · 2^{-N} ≤ ξ/4`, the rounded projection `Π(v)` of (64) is
within `ξ` of the Euclidean projection of `v` onto the closed unit ball `B₂ᵐ`. -/
theorem claim_7_7 (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 2) (m : ℕ) (v : Fin m → ℚ) (r : ℚ)
    (N : ℤ) (hr : AdmissibleRadius (η ^ 2 / 1024) v r)
    (hN : Real.sqrt (m : ℝ) * (2 : ℝ) ^ (-N) ≤ η ^ 2 / 1024 / 4) :
    ‖toE (roundedProjection v r N) - CalamaiMore.Convergence.proj (unitBall m) (toE v)‖ ≤
      η ^ 2 / 1024 := by sorry

end DetTerminalEmbedding1373.Real.Supplement
