-- Prove2me | Theorems.Thm_DetDLP_collision_energy_moment_bound
-- name    : DetDLP.collision_energy_moment_bound
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T10:17:21.517442+00:00
-- url     : https://prove2.me/theorems/c9eca435-f241-46e4-9dff-cc9ed895f2b6
-- title:
--   Collision energy of affine-interval factor blocks
-- statement:
--   Let $G$ be $E(\mathbb F_p)$ for a nonsingular Weierstrass curve with $p>3$, or $\mathbb F_p^\times$. Let $g=|G|$ and let $n$ count the eligible elements (all affine points in the curve case and all units in the multiplicative case). Assume $g\ge64$, $m\ge2$ and $n\ge4096m$. Let $q_* = \max(4096m,\lceil(16g)^{1/m}\rceil)$, $T=\lceil p q_*/n\rceil$, $q=nT/p$ and $\mu=q^m$. Choose the $m$ affine-interval blocks independently and uniformly according to the posted hash family. The elliptic-curve family has separate seeds for the two canonical $y$-parity classes.
--
--   For a seed $S$, write $C_S$ for the number of ordered pairs of block tuples with equal group sum or product. Then
--   $$\mathbb E C_S\le\mu+\frac{\mu^2}{n}\left((1+2/q)^m+4(2/q)^m\right).$$
--   This estimate allows pairs of distinct elliptic-curve points with the same abscissa and the same canonical ordinate parity.
-- source:
--   Adaptation of the counting argument in S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Lemma 3.2, pp. 12–13, allowing coincident hash keys on general Weierstrass models.

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

theorem collision_energy_moment_bound :
    (∀ (p m : ℕ) [Fact p.Prime], 3 < p → 2 ≤ m →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let gord := Fintype.card E.toAffine.Point
        let n := gord - 1
        64 ≤ gord → 4096 * m ≤ n →
        let T := hashThreshold p n m gord
        let q := qBlk p n T
        let μ := q ^ m
        (∑ S : ECSeed p m, (collisionEnergyAdd (ecFactorBlock E T S) : ℝ)) /
          (Fintype.card (ECSeed p m) : ℝ) ≤ μ + μ^2 / (n : ℝ) * ((1 + 2/q)^m + 4 * (2/q)^m)) ∧
    (∀ (p m : ℕ) [Fact p.Prime], 2 ≤ m →
      let gord := p - 1
      let n := p - 1
      64 ≤ gord → 4096 * m ≤ n →
      let T := hashThreshold p n m gord
      let q := qBlk p n T
      let μ := q ^ m
      (∑ S : FpSeed p m, (collisionEnergyMul (fpFactorBlock (p := p) T S) : ℝ)) /
        (Fintype.card (FpSeed p m) : ℝ) ≤ μ + μ^2 / (n : ℝ) * ((1 + 2/q)^m + 4 * (2/q)^m)) := by sorry

end DetDLP
