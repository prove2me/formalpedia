-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_prefix_product_action_inner_v1
-- name    : BraidsLinksMCG.artin_prefix_product_action_inner_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T14:24:25.328986+00:00
-- url     : https://prove2.me/theorems/6ae55664-d94a-4298-87af-120e28bf171b
-- title:
--   A prefix of the adjacent Artin generators has an explicit action
-- statement:
--   This child isolates the finite prefix-product computation used in Artin's free-group action. If the first k adjacent Artin generators act according to equation (1-14), their product sends a generator below the prefix boundary to the corresponding conjugation by x₀, sends the boundary generator to x₀, and fixes generators beyond the boundary. The statement is an independent finite induction over the prefix and does not assert the full-twist power identity.
-- source:
--   Birman, Braids, Links, and Mapping Class Groups, Chapter 1, equation (1-14), applied to a finite prefix of the ordered product of adjacent Artin generators.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_prefix_product_action_inner_v1
    (n : ℕ) (hn : 2 ≤ n)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      xi (sigma i) w = artinEndo n i w)
    (k : ℕ) (hk : k ≤ n - 1) (j : Fin n) :
    xi ((List.ofFn (fun i : Fin (n - 1) => sigma i)).take k).prod
        (FreeGroup.of j) =
      if h : j.val < k then
        FreeGroup.of ⟨0, by omega⟩ *
          FreeGroup.of ⟨j.val + 1, by omega⟩ *
          (FreeGroup.of ⟨0, by omega⟩)⁻¹
      else if h : j.val = k then
        FreeGroup.of ⟨0, by omega⟩
      else
        FreeGroup.of j := by sorry

end BraidsLinksMCG
