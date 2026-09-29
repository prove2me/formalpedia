-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_full_twist_action_inner_v2
-- name    : BraidsLinksMCG.artin_full_twist_action_inner_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T07:33:22.488974+00:00
-- url     : https://prove2.me/theorems/5d81f6ef-1df6-421d-a35d-9dc08c515967
-- title:
--   The Artin action of the full twist is global conjugation for n at least two
-- statement:
--   For $n \ge 2$, let $\xi$ be a homomorphism from the Artin braid group on $n$ strands to automorphisms of the free group on $n$ generators, and suppose that it sends each braid generator to the corresponding Artin automorphism. Then the full twist acts by conjugation with the global word $x_1\cdots x_n$:
--
--   $$
--   \xi\bigl((\sigma_1\cdots\sigma_{n-1})^n\bigr)(w)
--   =x_1\cdots x_n\,w\,(x_1\cdots x_n)^{-1}.
--   $$
--
--   The lower bound $n\ge2$ is essential. For $n=1$, the braid product is empty and its action is the identity, whereas conjugation by $x_1$ is not the identity. The parent centre theorem uses the stronger hypothesis $n\ge3$.
-- source:
--   Joan S. Birman, Braids, Links, and Mapping Class Groups, Chapter 1, equation (1-14) and Corollary 1.8.4; the boundary condition n ≥ 2 is required by the empty-product convention for the one-strand group.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_full_twist_action_inner_v2 (n : ℕ) (hn : 2 ≤ n)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      xi (sigma i) w = artinEndo n i w) :
    ∀ w : FreeGroup (Fin n),
      xi (sigmaProd n ^ n) w =
        freeWordProd n * w * (freeWordProd n)⁻¹ := by sorry

end BraidsLinksMCG
