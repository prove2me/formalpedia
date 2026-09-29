-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_centralizer_conj_form_common_power_v1
-- name    : BraidsLinksMCG.artin_centralizer_conj_form_common_power_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-24T16:48:55.607985+00:00
-- url     : https://prove2.me/theorems/7a99ac29-9852-4921-869f-9546d3b4652b
-- title:
--   The conjugators in the commuting Artin case are one global-word power
-- statement:
--   Assume the commuting free-group automorphism $\beta$ has already been shown to send each generator to a conjugate of a generator, and that it fixes the ordered global word $x_0x_1\cdots x_{n-1}$. This child records the remaining reduced-word step: the permutation and the individual conjugators are not independent. After using the adjacent Artin commutation equations and the fixed positive word, there is one integer $k$ such that every generator is sent to conjugation by the same global-word power: $$\beta(x_j)=(x_0x_1\cdots x_{n-1})^k x_j (x_0x_1\cdots x_{n-1})^{-k}.$$ The generator-conjugator hypothesis is isolated in the published child `BraidsLinksMCG.artin_centralizer_conj_form_v1`; this theorem contains only the subsequent common-power normalization.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 1, Theorem 1.9 and Corollary 1.8.4; the common global-word conjugator calculation in Artin's free-group argument.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_centralizer_conj_form_common_power_v1
    (n : ℕ) (hn : 3 ≤ n)
    (beta : MulAut (FreeGroup (Fin n)))
    (hcentral : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta (artinEndo n i w) = artinEndo n i (beta w))
    (hword : beta (freeWordProd n) = freeWordProd n)
    (hconj : ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
      ∀ j : Fin n,
        beta (FreeGroup.of j) =
          A j * FreeGroup.of (mu j) * (A j)⁻¹) :
    ∃ k : ℤ, ∀ j : Fin n,
      beta (FreeGroup.of j) =
        (freeWordProd n) ^ k * FreeGroup.of j *
          (freeWordProd n) ^ (-k) := by sorry

end BraidsLinksMCG
