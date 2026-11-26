-- Prove2me | Theorems.Thm_Erdos287_type_iii_common_residue_gcd
-- name    : Erdos287.type_iii_common_residue_gcd
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T04:42:45.68743+00:00
-- url     : https://prove2.me/theorems/afcc744d-e9e8-5047-89c2-01aad92c00bf
-- title:
--   Removal of a common unit residue from a Type III correlation
-- statement:
--   If rho_i n_i equals the same unit a modulo m and both n_i are units modulo m, then the gcd of rho_1 b_2 minus rho_2 b_1 with m equals the gcd of n_2 b_2 minus n_1 b_1 with m.
-- source:
--   Erdős Problem #287, mixed-residue Type III correlation. The cubic choice of b_i is used in the hyper-Kloosterman completion from Polymath, New equidistribution estimates of Zhang type, §6J.2.

import Mathlib

theorem Erdos287.type_iii_common_residue_gcd (m a n₁ n₂ ρ₁ ρ₂ b₁ b₂ : ℤ)
    (h₁ : ρ₁ * n₁ ≡ a [ZMOD m]) (h₂ : ρ₂ * n₂ ≡ a [ZMOD m])
    (ha : IsCoprime m a) (hn : IsCoprime m (n₁ * n₂)) :
    Int.gcd (ρ₁ * b₂ - ρ₂ * b₁) m = Int.gcd (n₂ * b₂ - n₁ * b₁) m := by sorry
