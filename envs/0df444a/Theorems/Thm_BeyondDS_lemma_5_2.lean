-- Prove2me | Theorems.Thm_BeyondDS_lemma_5_2
-- name    : BeyondDS.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:14:31.085265+00:00
-- url     : https://prove2.me/theorems/5440d05e-690e-4cc6-a46f-94394ed90947
-- title:
--   Lemma 5.2 — commit invariant
-- statement:
--   Consider any outcome of the compiler, with a perfectly correct scheme, any election law and any adversary, in which no signature is forged and every required dissemination delivery occurs. If a forever-honest player issues a commit for $b$ in iteration $r$, then:
--
--   1. no unforged record set contains a verifying iteration-$r$ certificate for $1-b$ ("even if it is assembled privately or after iteration $r$");
--   2. every forever-honest player's state frozen at a later Status stage has rank at least $r$ and bit $b$;
--   3. no unforged record set contains a verifying certificate for $1-b$ of a later rank.
--
--   Together with Lemma 5.3 this gives agreement and validity of the compiler.
--
--   **Formalization Note** An unforged record set is any set of records whose signatures verify under the honest keys and in which every signature of a forever-honest identity is on data that identity signed; it need not have been seen by an honest player.
--
--   Differences from the source:
--
--   - reading: "no certificate for 1 − b exists … even if it is assembled privately" → no unforged record set verifies a certificate for 1 − b; reason: a certificate assembled by anybody is a record set whose honest signatures were signed
--   - reading: "accepts a certificate for b of rank at least r before the next Status stage" → the state frozen at every later Status stage has rank ≥ r and bit b; reason: the state frozen at Status is the accepted certificate
--   - reading: "the required dissemination deliveries occur before any honest player halts" → every required delivery obligation of every call holds; reason: a recipient that has halted has no output and no obligation
--   - encoding: signatures → a perfectly correct scheme; reason: the standing assumption of the paper's model (decision 7)
--   - generalization: the late common election oracle of §§4.3, 5.1 (uniform, or within ζ of uniform, given the transcript) → any election law, a function of the transcript at the reveal boundary; reason: the conclusion holds whatever identity is elected, and the oracle is one such law
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Lemma 5.2, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_BeyondDS_DeliveryFail

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal
open Polynomial

namespace BeyondDS

/-- Lemma 5.2 (Commit invariant), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.17 (PDF 18): assume that no signatures are forged and that the required dissemination deliveries occur before any honest player halts. If a forever-honest
player issues a commit for `b` in iteration `r`, no certificate for `1 − b` exists at rank `r`, even if it is assembled privately or after iteration `r`. Every forever-honest player accepts a certificate for `b` of rank at least `r` before the next
Status stage, and no later certificate for `1 − b` exists.

**Formalization Note.** "Exists" quantifies over every record set `W` with honest-key-verifying signatures, in which each signature of a forever-honest identity is on data that identity signed, and not only over what an honest player saw. "Accepts before the next Status stage" is read off
the state `(h, bit)` the player froze at every later Status stage. -/
theorem lemma_5_2 (J : Params → ℕ) (S : Sig) (hS : S.Correct) (P : Params) (x : Bool)
    (E : List (Event P.n CMsg CSt) → PMF (Fin P.n)) (A : Adversary P.n CMsg CSt)
    (ω : Config P.n CMsg CSt A.σ) (hω : ω ∈ (exec (compiler J) S P x E A).support)
    (hF : ¬ Forge ω) (hD : Delivered P (J P) ω) (r : ℕ) (b : Bool) (hCommit : IssuedCommit P ω r b) :
    (∀ W, Unforged S P (J P) ω W → certValid (publicCtx P (J P) ω) W r (!b) = false) ∧
    (∀ i, ω.ForeverHonest i → ∀ r' h b', (r', h, b') ∈ (viewOf ω i).frozen → r < r' → (r : ℤ) ≤ h ∧ b' = b) ∧
    (∀ s, r < s → ∀ W, Unforged S P (J P) ω W → certValid (publicCtx P (J P) ω) W s (!b) = false) := by sorry

end BeyondDS
