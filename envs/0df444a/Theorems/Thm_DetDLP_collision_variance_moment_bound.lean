-- Prove2me | Theorems.Thm_DetDLP_collision_variance_moment_bound
-- name    : DetDLP.collision_variance_moment_bound
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T10:17:23.258317+00:00
-- url     : https://prove2.me/theorems/4138e246-0406-4d8d-8863-7cd88955e8ae
-- title:
--   Variance of the product of affine-interval block sizes
-- statement:
--   Let $G$ be $E(\mathbb F_p)$ for a nonsingular Weierstrass curve with $p>3$, or $\mathbb F_p^\times$. Let $g=|G|$ and let $n$ count the eligible elements (all affine points in the curve case and all units in the multiplicative case). Assume $g\ge64$, $m\ge2$ and $n\ge4096m$. Let $q_* = \max(4096m,\lceil(16g)^{1/m}\rceil)$, $T=\lceil p q_*/n\rceil$, $q=nT/p$ and $\mu=q^m$. Choose the $m$ affine-interval blocks independently and uniformly according to the posted hash family. The elliptic-curve family has separate seeds for the two canonical $y$-parity classes.
--
--   Write $W_S=\prod_i |F_i(S)|$ for the number of block tuples. Then
--   $$\mathbb E (W_S-\mu)^2\le\mu^2\left((1+2/q)^m-1\right).$$
--   This variance estimate allows for a shared hash key within a pair of inverse elliptic-curve points.
-- source:
--   Adaptation of the counting argument in S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Lemma 3.2, pp. 12–13, allowing coincident hash keys on general Weierstrass models.

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

theorem collision_variance_moment_bound :
    (∀ (p m : ℕ) [Fact p.Prime], 3 < p → 2 ≤ m →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let gord := Fintype.card E.toAffine.Point
        let n := gord - 1
        64 ≤ gord → 4096 * m ≤ n →
        let T := hashThreshold p n m gord
        let q := qBlk p n T
        let μ := q ^ m
        (∑ S : ECSeed p m, ((productSize (ecFactorBlock E T S) : ℝ) - μ) ^ 2) /
          (Fintype.card (ECSeed p m) : ℝ) ≤ μ^2 * ((1 + 2/q)^m - 1)) ∧
    (∀ (p m : ℕ) [Fact p.Prime], 2 ≤ m →
      let gord := p - 1
      let n := p - 1
      64 ≤ gord → 4096 * m ≤ n →
      let T := hashThreshold p n m gord
      let q := qBlk p n T
      let μ := q ^ m
      (∑ S : FpSeed p m, ((productSize (fpFactorBlock (p := p) T S) : ℝ) - μ) ^ 2) /
        (Fintype.card (FpSeed p m) : ℝ) ≤ μ^2 * ((1 + 2/q)^m - 1)) := by sorry

end DetDLP
