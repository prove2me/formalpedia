-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_centralizer_abelianization_pm_v1
-- name    : BraidsLinksMCG.artin_centralizer_abelianization_pm_v1
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-29T12:42:15.815822+00:00
-- url     : https://prove2.me/theorems/e7419006-c24c-41cf-86a0-96d20406f95c
-- title:
--   A commuting Artin automorphism induces plus-or-minus identity on abelianization
-- statement:
--   Let beta be an automorphism of the free group F_n on x_0,...,x_{n-1} with n >= 3, commuting with every adjacent Artin automorphism sigma_i (beta(sigma_i(w)) = sigma_i(beta(w)) for all i, w). Then the induced map on the abelianization F_n^ab = Z^n is either the identity or minus the identity, with a single global choice of sign: for every j, the class of beta(x_j) is either the class of x_j or the class of x_j^{-1}. Proof ingredients: each sigma_i abelianizes to the adjacent transposition (i i+1), so the induced automorphism of Z^n commutes with all adjacent transpositions; elementary linear algebra (M = d*I + g*(J-I), det = +-1, n >= 3 forces g = 0) gives +-I. This is the provable first step of the Dyer-Grossman centralizer analysis; the deep second step (conjugacy of generator images) is isolated in the sibling node BraidsLinksMCG.artin_centralizer_conj_of_abelianization_pm_v1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_centralizer_abelianization_pm_v1
    (n : ℕ) (hn : 3 ≤ n)
    (beta : MulAut (FreeGroup (Fin n)))
    (hcentral : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta (artinEndo n i w) = artinEndo n i (beta w)) :
    (∀ j : Fin n, Abelianization.of (beta (FreeGroup.of j)) =
      Abelianization.of (FreeGroup.of j)) ∨
    (∀ j : Fin n, Abelianization.of (beta (FreeGroup.of j)) =
      Abelianization.of ((FreeGroup.of j)⁻¹)) := by sorry

end BraidsLinksMCG
