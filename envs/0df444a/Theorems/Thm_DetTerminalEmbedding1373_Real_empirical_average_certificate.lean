-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_empirical_average_certificate
-- name    : DetTerminalEmbedding1373.Real.empirical_average_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:31.05774+00:00
-- url     : https://prove2.me/theorems/77af3cb2-4a40-4ca1-8c79-2f938e0952b5
-- title:
--   Lemma 3.2 — finite empirical-average certificate
-- statement:
--   Let $Y\subseteq B_2^d$ be finite, $0<\eta\le1/2$, and $2\le S\le\eta^{-2}$. For $s\ge1$, let $E_s(Y)$ be the averages of all ordered length-$s$ samples from $Y$, with repetition, and set $\delta_s=\frac18\min\{\eta\sqrt s,\eta^2S\}$. If a linear map $A:E_d\to E_m$ satisfies
--
--   $$|\|Az\|^2-\|z\|^2|\le\delta_s\|z\|^2\qquad(z\in E_s(Y),\ 1\le s\le S),$$
--
--   then $|\|Az\|-\|z\||<\eta$ for every $z\in\operatorname{conv}(Y)$. The hypothesis includes zero averages, and the conclusion covers the entire convex hull. This is the common certificate connecting the finite tests to all queries.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and finite indexed vectors or signs → EuclideanSpace over Fin indices and Boolean signs; reason: the Euclidean norm and every real coordinate are retained, with +1 represented by true
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 11, Lemma 3.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_potential

set_option autoImplicit false
open scoped ENNReal

namespace DetTerminalEmbedding1373.Real

/-- Lemma 3.2, p. 11. Includes every real point of the convex hull and zero
empirical averages, with strict additive norm error. -/
theorem empirical_average_certificate {d m : ℕ} (Y : Set (E d)) (hfin : Y.Finite)
    (hball : Y ⊆ unitBall d) (η : ℝ) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (S : ℕ) (hS : 2 ≤ S) (hSmax : (S : ℝ) ≤ 1 / η ^ 2)
    (A : E d →ₗ[ℝ] E m)
    (htest : ∀ s ∈ Finset.Icc 1 S, ∀ z ∈ empiricalSet Y s,
      |‖A z‖ ^ 2 - ‖z‖ ^ 2| ≤ tolerance η S s * ‖z‖ ^ 2) :
    ∀ z ∈ convexHull ℝ Y, |‖A z‖ - ‖z‖| < η := by sorry

end DetTerminalEmbedding1373.Real
