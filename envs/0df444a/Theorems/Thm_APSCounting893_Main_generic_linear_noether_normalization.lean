-- Prove2me | Theorems.Thm_APSCounting893_Main_generic_linear_noether_normalization
-- name    : APSCounting893.Main.generic_linear_noether_normalization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:01:47.493277+00:00
-- url     : https://prove2.me/theorems/c3c3c422-9e14-46b3-b91a-18da2c87cbe5
-- title:
--   Lemma 3.15 — Generic linear Noether normalization
-- statement:
--   Let $Y\subseteq\mathbb C^{n+1}$ be nonempty, irreducible and closed, with dimension $n\ge1$. A nonempty Zariski-open set of coefficient vectors $c\in\mathbb C^n$ gives
--
--   $$\pi_c(y)=(y_1-c_1y_{n+1},\ldots,y_n-c_ny_{n+1})$$
--
--   finite and surjective on $Y$. Its coordinate-ring pullback is injective; $\mathbb C[Y]$ is finite as a module over the pullback image; and every coordinate function is integral over that image. All four conclusions are retained. This is the prescribed generic linear normalization, rather than an unspecified integral polynomial-algebra embedding.
--
--   Differences from the source:
--   - encoding: coordinate-ring injectivity, module finiteness and integrality → polynomial-representative tests for injectivity, finite module generation and monic coordinate equations; reason: equalities modulo the actual vanishing ideal are exactly pointwise equalities on Y
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Lemma 3.15, p. 15, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_Geometry

set_option autoImplicit false

namespace APSCounting893.Main

theorem generic_linear_noether_normalization (n : ℕ) (hn : 0 < n) (Y : Set (Affine ℂ (n + 1)))
    (hirr : IrreducibleAffine Y)
    (hdim : RSCapacity.algDim Y = ((n : ℕ∞) : WithBot ℕ∞)) :
    ∃ O : Set (Affine ℂ n), O.Nonempty ∧ RelativeOpen Set.univ O ∧
      ∀ c ∈ O, IsNormalization Y c := by sorry

end APSCounting893.Main
