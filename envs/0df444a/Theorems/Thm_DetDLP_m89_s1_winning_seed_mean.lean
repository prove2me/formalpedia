-- Prove2me | Theorems.Thm_DetDLP_m89_s1_winning_seed_mean
-- name    : DetDLP.m89_s1_winning_seed_mean
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T20:22:28.992131+00:00
-- url     : https://prove2.me/theorems/5ef800eb-269b-4c5e-9a12-3440a567bb7d
-- title:
--   A full winning seed prefix has collision potential at most the uniform average
-- statement:
--   For either affine-interval seed representation, fix a prime, a block count, and, in the additive case, a Weierstrass curve over the prime field. At each successive seed bit follow a nonempty child of smaller mean collision potential, breaking ties to the left. Every seed in the resulting full prefix has potential at most the mean over all seeds. This statement uses the actual fixed-width packing of the $2m$ or $4m$ seed coordinates, not an assumption that the supplied encoding separates seeds.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 Proof of Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_M89_S1_Queries

set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_s1_winning_seed_mean :
    (∀ (p m : ℕ) [Fact p.Prime] (S : FpSeed p m),
      S ∈ winners fpBits (fpCost p m) →
      fpCost p m S ≤ (∑ s : FpSeed p m, fpCost p m s) / (Fintype.card (FpSeed p m) : ℝ)) ∧
    (∀ (p m : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (S : ECSeed p m),
      S ∈ winners ecBits (ecCost E (m := m)) →
      ecCost E S ≤ (∑ s : ECSeed p m, ecCost E s) / (Fintype.card (ECSeed p m) : ℝ)) := by sorry
