-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_centralizer_conj_form_v1
-- name    : BraidsLinksMCG.artin_centralizer_conj_form_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-24T15:53:00.242189+00:00
-- url     : https://prove2.me/theorems/c92631b0-212c-4dc3-ac18-ca3242e9e976
-- title:
--   A commuting Artin automorphism has generator-conjugator form
-- statement:
--   Let $\beta$ be an automorphism of the free group $F_n$ on the letters $x_0,\ldots,x_{n-1}$ with $n\ge 3$. Assume that $\beta$ commutes with every adjacent Artin automorphism and fixes the ordered product $x_0x_1\cdots x_{n-1}$. This child isolates the necessary first step of Artin's free-group classification: there are a permutation $\mu$ of the generator indices and words $A_0,\ldots,A_{n-1}$ such that
--   $$eta(x_j)=A_jx_{\mu(j)}A_j^{-1}$$
--   for every $j$. The proof is a reduced-word calculation using the adjacent commutation equations; it does not yet identify the permutation or the common power represented by the conjugators.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 1, Theorem 1.9 and equation (1-14), pp. 25 and 30; the conjugacy-class condition preceding Artin's sufficiency theorem.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_centralizer_conj_form_v1
    (n : ℕ) (hn : 3 ≤ n)
    (beta : MulAut (FreeGroup (Fin n)))
    (hcentral : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta (artinEndo n i w) = artinEndo n i (beta w))
    (hword : beta (freeWordProd n) = freeWordProd n) :
    ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
      ∀ j : Fin n,
        beta (FreeGroup.of j) =
          A j * FreeGroup.of (mu j) * (A j)⁻¹ := by sorry

end BraidsLinksMCG
