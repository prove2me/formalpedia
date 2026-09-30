-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_centralizer_conj_perm_index_v1
-- name    : BraidsLinksMCG.artin_centralizer_conj_perm_index_v1
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-29T11:44:44.394808+00:00
-- url     : https://prove2.me/theorems/c040017d-d5a1-4a4d-b3d7-653c3cf9358e
-- title:
--   A commuting Artin automorphism permutes the generators up to conjugacy
-- statement:
--   Let beta be an automorphism of the free group F_n on x_0,...,x_{n-1} with n >= 3, commuting with every adjacent Artin automorphism sigma_i (i.e. beta(sigma_i(w)) = sigma_i(beta(w)) for all i and w). Then there is a permutation mu of the generator indices such that every generator image beta(x_j) is a conjugate of a single generator: beta(x_j) = A_j * x_{mu(j)} * A_j^{-1} for some word A_j. The proof is Artin's reduced-word calculation: comparing reduced words in beta(sigma_i(x_j)) = sigma_i(beta(x_j)) for adjacent i forces each beta(x_j) to be a conjugate of one generator, and the index assignment is bijective because beta is an automorphism (abelianization sends conjugates to standard basis vectors, so distinct generators cannot collapse to the same index). This child isolates the deep combinatorial input of BraidsLinksMCG.artin_centralizer_conj_form_v1 (c92631b0); the assembly over it is a pure existential repackaging. Reference: Joan S. Birman, Braids, Links, and Mapping Class Groups, Chapter 1, Theorem 1.9 and equation (1-14), pp. 25 and 30.

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_centralizer_conj_perm_index_v1
    (n : ℕ) (hn : 3 ≤ n)
    (beta : MulAut (FreeGroup (Fin n)))
    (hcentral : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta (artinEndo n i w) = artinEndo n i (beta w)) :
    ∃ mu : Equiv.Perm (Fin n), ∀ j : Fin n, ∃ A : FreeGroup (Fin n),
      beta (FreeGroup.of j) = A * FreeGroup.of (mu j) * A⁻¹ := by sorry

end BraidsLinksMCG
