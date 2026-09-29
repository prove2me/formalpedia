-- Prove2me | Theorems.Thm_BraidsLinksMCG_cor_1_8_3_artin_representation_faithful
-- name    : BraidsLinksMCG.cor_1_8_3_artin_representation_faithful
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T19:00:29.697674+00:00
-- url     : https://prove2.me/theorems/479d7c79-e900-4f2c-84b8-02c848c51080
-- title:
--   Corollary 1.8.3: $B_n$ acts faithfully on the free group $F_n$
-- statement:
--   **Corollary 1.8.3 (Artin's representation).** The braid group $B_n$ has a faithful
--   representation as a group of automorphisms of a free group $F_n = \langle x_1, \dots, x_n\rangle$
--   of rank $n$, induced by the assignment (1-14)
--
--   $$\sigma_i : \quad x_i \mapsto x_i x_{i+1} x_i^{-1}, \qquad x_{i+1} \mapsto x_i, \qquad
--     x_j \mapsto x_j \quad (j \neq i, i+1).$$
--
--   Formally: there is a group homomorphism $\xi$ from $B_n$ to the automorphism group of $F_n$ whose
--   value at each generator $\sigma_i$ acts on $F_n$ exactly as the endomorphism (1-14), and $\xi$ is
--   injective. The first half is the well-definedness of $\xi$ — the braid relations must be
--   respected — and the second half is faithfulness, so that a braid is completely determined by the
--   automorphism it induces.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, p. 25, Corollary 1.8.3 with equation (1-14)

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem cor_1_8_3_artin_representation_faithful (n : ℕ) :
    ∃ xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)),
      (∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w) ∧
        Function.Injective xi := by sorry

end BraidsLinksMCG
