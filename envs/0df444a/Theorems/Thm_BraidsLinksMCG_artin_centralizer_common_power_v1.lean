-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_centralizer_common_power_v1
-- name    : BraidsLinksMCG.artin_centralizer_common_power_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-24T15:57:06.132281+00:00
-- url     : https://prove2.me/theorems/dd1e740c-ebbc-4f93-8cc0-929b1d3792d3
-- title:
--   The common conjugator for a commuting Artin automorphism is a global-word power
-- statement:
--   Let $\beta$ be an automorphism of the free group $F_n$ on the letters $x_0,\ldots,x_{n-1}$ with $n\ge 3$. Assume that $\beta$ commutes with every adjacent Artin automorphism and fixes the ordered product $x_0x_1\cdots x_{n-1}$. This child isolates the final reduced-word step of Artin's classification: there is one integer $k$ such that every generator is sent to its conjugation by the same global-word power,
--   $$eta(x_j)=(x_0x_1\cdots x_{n-1})^k x_j (x_0x_1\cdots x_{n-1})^{-k}.$$
--   The original centralizer theorem follows by equality of homomorphisms on generators; this child records only the generator-level statement so the common-power calculation can be proved independently.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 1, Theorem 1.9 and Corollary 1.8.4, pp. 30 and 28; the common global-word conjugator in Artin's free-group argument.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_centralizer_common_power_v1
    (n : ℕ) (hn : 3 ≤ n)
    (beta : MulAut (FreeGroup (Fin n)))
    (hcentral : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta (artinEndo n i w) = artinEndo n i (beta w))
    (hword : beta (freeWordProd n) = freeWordProd n) :
    ∃ k : ℤ, ∀ j : Fin n,
      beta (FreeGroup.of j) =
        (freeWordProd n) ^ k * FreeGroup.of j *
          (freeWordProd n) ^ (-k) := by sorry

end BraidsLinksMCG
