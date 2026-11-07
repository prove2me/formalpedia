-- Prove2me | Theorems.Thm_BeyondDS_lemma_5_1
-- name    : BeyondDS.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:14:21.963284+00:00
-- url     : https://prove2.me/theorems/6d63ac3c-2edc-4c71-983c-c482d237ffc5
-- title:
--   Lemma 5.1 with (20) — normalized payloads have $O(n^2J^2)$ records, and normalization preserves verification
-- statement:
--   1. There is an absolute constant $C$ such that, for all public data with $J\ge1$, $n\ge1$, every store of records whose fields have bit length at most $L\ge1$, and every duplicate-free list of records of the normalized store, the list has at most $Cn^2J^2$ records and its code has at most $Cn^2J^2L$ bits.
--   2. Normalization preserves every verification predicate used by the compiler: certificates, termination certificates, supports, headers, prepared proposals and counted voters are the same in the normalized store as in the domain-checked store; and every closure computed in the normalized store consists of its records.
--   3. (20) In every outcome of stand-alone dissemination from any prefix, the distinct retained payload and acknowledgement records number at most $(n+1)L_P+L_A$, where $L_P$ counts the distinct payload records among initial source payloads and adversarial messages (including those inside acknowledgements) and $L_A$ the distinct acknowledgement records supplied by the adversary.
--
--   "The encoding requires no collision-resistant hash assumption": no hash occurs in the model. These bounds are what make the efficiency clause of the goal true for the compiler.
--
--   Differences from the source:
--
--   - reading: "every normalized compiler payload" → every duplicate-free list of records of the normalized store; reason: the compiler's outgoing payloads are closures in the normalized store, which part 2 places there
--   - reading: L, "a polynomial upper bound on the bit length of a header, its signature, and a graph reference" → a bound L ≥ 1 on every field of every record, with J ≥ 1 and n ≥ 1; reason: at J = 0 the sender and terminal records exist while n²J² = 0, so the lemma presumes an iteration
--   - reading: "preserves every verification predicate" → equality of each predicate on the normalized and on the domain-checked store; reason: normalization begins with the public domain checks of p.15
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Lemma 5.1, p.16 (PDF p.17); eq. (20), p.27 (PDF p.28)

import Mathlib
import Definitions.Def_BeyondDS_DeliveryFail

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal
open Polynomial

namespace BeyondDS

/-- Lemma 5.1 (Polynomial evidence encoding), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.16 (PDF 17), with the record count (20), p.27 (PDF 28). With iteration cap `J`, every normalized compiler payload contains `O(n²J²)` signature records
and references and has bit length `O(n²J²L)`, and normalization preserves every verification predicate, vote guard and certificate used by the compiler. And a dissemination call contains at most `(n + 1)L_P + L_A`
distinct retained payload and acknowledgement records, `L_P` counting "distinct payload records among initial source payloads and adversarial messages" and `L_A` "distinct acknowledgement records supplied by the adversary".

**Formalization Note.** A normalized payload is any list without repeats of records of the normalized store; the closures the compiler sends are of this form, which the last clauses say. `L` bounds the bits of a record's header, signature and reference. "The encoding requires
no collision-resistant hash assumption" has no formal content here: no hash occurs in the model. `1 ≤ J` and `1 ≤ L`: at `J = 0` the sender and terminal records exist while `n²J² = 0`. The comparison is with the domain-checked store, since normalization first applies the domain checks
of p.15. -/
theorem lemma_5_1 :
    (∃ C : ℕ, ∀ (x : EvCtx) (S : List EvRec) (L : ℕ), 1 ≤ x.J → 1 ≤ x.n → 1 ≤ L →
      (∀ e ∈ S, ∀ w ∈ e.fields, w.length ≤ L) →
      let D := S.filter (EvRec.inDomain x)
      let N := normalize x S
      (∀ body : List EvRec, body.Nodup → (∀ e ∈ body, e ∈ N) →
        body.length ≤ C * x.n ^ 2 * x.J ^ 2 ∧ (encRecs body).length ≤ C * x.n ^ 2 * x.J ^ 2 * L) ∧
      (∀ r b, certValid x N r b = certValid x D r b) ∧
      (∀ r b, termValid x N r b = termValid x D r b) ∧
      (∀ b k, supportValid x N b k = supportValid x D b k) ∧
      (∀ q, headerValid x N q = headerValid x D q) ∧
      (∀ q, preparedValid x N q = preparedValid x D q) ∧
      (∀ r b j, j ∈ voters x N r b ↔ j ∈ voters x D r b) ∧
      (∀ r b e, e ∈ certClosure x N r b → e ∈ N) ∧
      (∀ q e, e ∈ preparedClosure x N q → e ∈ N) ∧
      (∀ r b e, e ∈ termClosure x N r b → e ∈ N)) ∧
    (∀ (sid : ℕ) (x : (P : Params) → Fin P.n → Str) (S : Sig) (P : Params) (y : Bool)
      (E : List (Event P.n (Envelope Str) (ProgState (Envelope Str) (LS Str))) → PMF (Fin P.n))
      (A : Adversary P.n (Envelope Str) (ProgState (Envelope Str) (LS Str))) (a : A.σ)
      (pk sk : Fin P.n → Str) (C₀ : Finset (Fin P.n)) (signLog : List (Fin P.n × Str))
      (obs : List (Obs P.n (Envelope Str) (ProgState (Envelope Str) (LS Str)))) (ω),
      ω ∈ (execFrom (dissem sid x) S P E A (Config.start (dissem sid x) P y pk sk C₀ signLog a obs)).support →
      (retainedPay ω).toFinset.card + (retainedAck ω).toFinset.card ≤
        (P.n + 1) * (initialPayloads sid ω ++ advPayloads ω).toFinset.card + (advAcks ω).toFinset.card) := by sorry

end BeyondDS
