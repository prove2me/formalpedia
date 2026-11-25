-- Prove2me | Theorems.Thm_DetDLP_lemma_3_2_collision_potential
-- name    : DetDLP.lemma_3_2_collision_potential
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T09:20:47.582199+00:00
-- url     : https://prove2.me/theorems/77abf563-a0e5-41df-a72c-49b6fa9efcaa
-- title:
--   Lemma 3.2: Expectation Bound $\mathbb{E}[\Phi(S)] \le 373/336$ for the Collision Potential
-- statement:
--   Let $p$ be a prime and $m \ge 2$ an integer, and consider either (1) an elliptic Weierstrass curve $E/\mathbb{F}_p$ ($p > 3$) with $g_{\mathrm{ord}} = |E(\mathbb{F}_p)|$ and $n = g_{\mathrm{ord}} - 1$, or (2) the multiplicative group $\mathbb{F}_p^*$ with $g_{\mathrm{ord}} = n = p - 1$. Assume the general regime $g_{\mathrm{ord}} \ge 64$ and $4096 m \le n$, and set $T = \lceil p q_* / n \rceil$ and $\mu = (nT/p)^m$ where $q_* = \max\{4096 m, \lceil (16 g_{\mathrm{ord}})^{1/m} \rceil\}$. Then the uniform average of the collision potential $\Phi(S) = (g_{\mathrm{ord}} C_S + 64(W_S - \mu)^2)/\mu^2$ over all affine-interval hash seeds $S$ satisfies
--
--   $$\mathbb{E}_{S}[\Phi(S)] \le \frac{373}{336} < \frac{64}{57}.$$
--
--   This purely combinatorial second-moment bound guarantees by Cauchy–Schwarz that conditional-expectation derandomization finds a seed whose $m$-fold sumset covers at least $7/8$ of the group.
--
--   **Formalization Note** Stated purely algebraically/combinatorially over finite seed spaces `ECSeed p m` and `FpSeed p m`, with no Turing-machine dependencies.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.2, Lemma 3.2 (pp. 12–13)

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

theorem lemma_3_2_collision_potential :
    (∀ (p m : ℕ) [Fact p.Prime], 3 < p → 2 ≤ m →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let gord := Fintype.card E.toAffine.Point
        let n := gord - 1
        64 ≤ gord → 4096 * m ≤ n →
        let T := hashThreshold p n m gord
        let μ := (qBlk p n T) ^ m
        (∑ S : ECSeed p m, collisionPotentialAdd μ (ecFactorBlock E T S)) /
          (Fintype.card (ECSeed p m) : ℝ) ≤ (373 : ℝ) / 336) ∧
    (∀ (p m : ℕ) [Fact p.Prime], 2 ≤ m →
      let gord := p - 1
      let n := p - 1
      64 ≤ gord → 4096 * m ≤ n →
      let T := hashThreshold p n m gord
      let μ := (qBlk p n T) ^ m
      (∑ S : FpSeed p m, collisionPotentialMul μ (fpFactorBlock (p := p) T S)) /
        (Fintype.card (FpSeed p m) : ℝ) ≤ (373 : ℝ) / 336) := by sorry

end DetDLP
