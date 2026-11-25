-- Prove2me | Theorems.Thm_DetDLP_w3_small_prime_bound
-- name    : DetDLP.w3_small_prime_bound
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:32:33.336448+00:00
-- url     : https://prove2.me/theorems/ce37f06b-80c6-473a-9654-890049b3088d
-- title:
--   A uniform field bound in the scan regime
-- statement:
--   Whenever the large-instance guard fails for either native group, the prime field has order at most $2^{32}$. For elliptic curves this conclusion uses the order of the affine point group and requires characteristic greater than three. This bounds the domain of the small-instance scan uniformly.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, equations (4.1)–(4.5) and proof of Theorem 1.1, pp. 13–16; referee revisions R1 and R2.

import Definitions.Def_DetDLP_W3_Driver
set_option autoImplicit false
open DetDLP

theorem DetDLP.w3_small_prime_bound :
    (∀ (p : ℕ) [Fact p.Prime], ¬w3_large p (p-1) → p ≤ 2^32) ∧
    (∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
      letI := ecPointFintype E; ¬w3_large p (Fintype.card E.toAffine.Point) → p ≤ 2^32) := by sorry
