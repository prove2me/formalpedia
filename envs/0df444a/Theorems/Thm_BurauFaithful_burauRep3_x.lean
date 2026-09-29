-- Prove2me | Theorems.Thm_BurauFaithful_burauRep3_x
-- name    : BurauFaithful.burauRep3_x
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-25T03:18:53.656501+00:00
-- url     : https://prove2.me/theorems/2eb43c63-6acb-4f8f-827e-ec0d57718b14
-- title:
--   Explicit Burau matrix of σ₁σ₂σ₁ in degree three
-- statement:
--   The unreduced Burau matrix of the braid σ₁σ₂σ₁ in B₃ is the explicit 3×3 matrix over ℤ[t,t⁻¹] with rows [1-t, t(1-t), t²], [1-t, t, 0], [1,0,0].

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BurauFaithful_UnreducedBurau

namespace BurauFaithful

theorem burauRep3_x :
    (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
      BraidsLinksMCG.sigma ⟨1, by decide⟩ * BraidsLinksMCG.sigma ⟨0, by decide⟩)).1 =
      ![![1 - LaurentPolynomial.T 1,
          LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T 1),
          LaurentPolynomial.T 1 ^ 2],
        ![1 - LaurentPolynomial.T 1, LaurentPolynomial.T 1, 0],
        ![1, 0, 0]] := by sorry

end BurauFaithful
