-- Prove2me | Theorems.Thm_BeyondDS_lemma_5_3
-- name    : BeyondDS.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:14:31.021171+00:00
-- url     : https://prove2.me/theorems/eb720a1b-e81b-4ecd-9258-431ac3b6d386
-- title:
--   Lemma 5.3 — broadcast validity
-- statement:
--   Under the hypotheses of Lemma 5.2 (no forgery, every required delivery), if the designated sender is forever honest with input $b$, then every termination certificate in an unforged record set has bit $b$.
--
--   Differences from the source:
--
--   - reading: "every termination certificate" → every verifying termination certificate in an unforged record set; reason: as in Lemma 5.2
--   - encoding: signatures → a perfectly correct scheme; reason: the standing assumption of the paper's model
--   - generalization: the late common election oracle of §§4.3, 5.1 (uniform, or within ζ of uniform, given the transcript) → any election law, a function of the transcript at the reveal boundary; reason: the conclusion holds whatever identity is elected, and the oracle is one such law
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Lemma 5.3, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_BeyondDS_DeliveryFail

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal
open Polynomial

namespace BeyondDS

/-- Lemma 5.3 (Broadcast validity), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.17 (PDF 18): under the hypotheses of Lemma 5.2, if the designated sender is forever honest with input `b`, every termination certificate has bit `b`. -/
theorem lemma_5_3 (J : Params → ℕ) (S : Sig) (hS : S.Correct) (P : Params) (x : Bool)
    (E : List (Event P.n CMsg CSt) → PMF (Fin P.n)) (A : Adversary P.n CMsg CSt)
    (ω : Config P.n CMsg CSt A.σ) (hω : ω ∈ (exec (compiler J) S P x E A).support)
    (hF : ¬ Forge ω) (hD : Delivered P (J P) ω) (hSender : ω.ForeverHonest P.sender) :
    ∀ W, Unforged S P (J P) ω W → ∀ r, termValid (publicCtx P (J P) ω) W r (!x) = false := by sorry

end BeyondDS
