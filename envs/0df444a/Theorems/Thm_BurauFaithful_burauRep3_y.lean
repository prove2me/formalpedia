-- Prove2me | Theorems.Thm_BurauFaithful_burauRep3_y
-- name    : BurauFaithful.burauRep3_y
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-25T03:18:42.417115+00:00
-- url     : https://prove2.me/theorems/66e9f4ac-ebc7-4f7d-ac3d-c6964745bd40
-- title:
--   Explicit Burau matrix of σ₁σ₂ in degree three
-- statement:
--   The unreduced Burau matrix of the braid σ₁σ₂ in B₃ is the explicit 3×3 matrix over ℤ[t,t⁻¹] with rows [1-t, t(1-t), t²], [1,0,0], [0,1,0].

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BurauFaithful_UnreducedBurau

namespace BurauFaithful

theorem burauRep3_y :
    (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
      BraidsLinksMCG.sigma ⟨1, by decide⟩)).1 =
      ![![1 - LaurentPolynomial.T 1,
          LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T 1),
          LaurentPolynomial.T 1 ^ 2],
        ![1, 0, 0],
        ![0, 1, 0]] := by sorry

end BurauFaithful
