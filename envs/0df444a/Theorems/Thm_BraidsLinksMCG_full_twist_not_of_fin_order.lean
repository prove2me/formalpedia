-- Prove2me | Theorems.Thm_BraidsLinksMCG_full_twist_not_of_fin_order
-- name    : BraidsLinksMCG.full_twist_not_of_fin_order
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-29T10:45:41.723736+00:00
-- url     : https://prove2.me/theorems/c71a4e20-7107-4e42-ac89-17d888cc8405
-- title:
--   The full twist has infinite order for n >= 3 strands
-- statement:
--   For n >= 3 strands, the full twist (sigma_1 ... sigma_{n-1})^n in the Artin braid group B_n is not of finite order. Proof: the exponent-sum homomorphism epsilon : B_n -> Multiplicative Z (proved in-mission as braid_exponent_sum_hom, 168ee371) sends each Artin generator to ofAdd 1, hence sends (sigmaProd n)^n to ofAdd (n*(n-1)), which is nonzero for n >= 3; but any finite-order element maps to 1 under a monoid hom. This is the missing second conjunct of cor_1_8_4_center_braid_group (96adf110): the center equals the zpowers of the full twist AND the full twist has infinite order.

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem full_twist_not_of_fin_order (n : ℕ) (hn : 3 ≤ n) :
    ¬ IsOfFinOrder ((sigmaProd n) ^ n) := by sorry

end BraidsLinksMCG
