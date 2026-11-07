-- Prove2me | Theorems.Thm_BeyondDS_section_8_2
-- name    : BeyondDS.section_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:14:07.016935+00:00
-- url     : https://prove2.me/theorems/fa2902fe-e7fb-4f9f-97e9-6a1842a454ed
-- title:
--   §8.2 — terminal mode preserves the commit invariant; all termination certificates share one bit
-- statement:
--   For the compiler with the terminal procedure, on every outcome with no forgery and every required delivery:
--
--   1. any two verifying termination certificates in unforged record sets have the same bit, "even if some are initially hidden or disclosed during later stages";
--   2. if the sender is forever honest with input $x$, no unforged record set verifies a termination certificate for $1-x$ ("The rank-0 argument of Lemma 5.3 continues to prove sender validity").
--
--   This is what the proof of Theorem 8 calls "established above".
--
--   Differences from the source:
--
--   - reading: "all verifying termination certificates" → all verifying termination certificates in unforged record sets; reason: as in Lemma 5.2
--   - reading: the setting of §8.2, successful dissemination → no forgery and every required delivery obligation; reason: the hypotheses of Lemma 5.2, which §8.2 extends
--   - generalization: the late common election oracle of §§4.3, 5.1 (uniform, or within ζ of uniform, given the transcript) → any election law, a function of the transcript at the reveal boundary; reason: the conclusion holds whatever identity is elected, and the oracle is one such law
--   - encoding: signatures → a perfectly correct scheme; reason: the standing assumption of the paper's model (decision 7)
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §8.2, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_BeyondDS_DeliveryFail

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal
open Polynomial

namespace BeyondDS

/-- The common termination bit, Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), §8.2, p.30 (PDF 31): with terminal mode in force and successful dissemination, "all verifying termination certificates have the same bit, even if some are initially hidden or disclosed during later stages. The rank-0 argument of Lemma 5.3
continues to prove sender validity."

**Formalization Note.** "All verifying termination certificates" quantifies over every unforged record set, as in Lemma 5.2. -/
theorem section_8_2 (J : Params → ℕ) (S : Sig) (hS : S.Correct) (P : Params) (x : Bool)
    (E : List (Event P.n CMsg CSt) → PMF (Fin P.n)) (A : Adversary P.n CMsg CSt)
    (ω : Config P.n CMsg CSt A.σ) (hω : ω ∈ (exec (compiler J) S P x E A).support)
    (hF : ¬ Forge ω) (hD : Delivered P (J P) ω) :
    (∀ W W', Unforged S P (J P) ω W → Unforged S P (J P) ω W' → ∀ r r' b b',
      termValid (publicCtx P (J P) ω) W r b = true → termValid (publicCtx P (J P) ω) W' r' b' = true → b = b') ∧
    (ω.ForeverHonest P.sender → ∀ W, Unforged S P (J P) ω W → ∀ r, termValid (publicCtx P (J P) ω) W r (!x) = false) := by sorry

end BeyondDS
