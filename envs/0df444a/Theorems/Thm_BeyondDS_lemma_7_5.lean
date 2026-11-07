-- Prove2me | Theorems.Thm_BeyondDS_lemma_7_5
-- name    : BeyondDS.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:57.964202+00:00
-- url     : https://prove2.me/theorems/0abd6c26-b3bd-4f62-84ec-e77f3ce248bb
-- title:
--   Lemma 7.5 with Corollary 7.6 — two rounds deliver from $t+1$ witnesses, except with probability $\delta_{fin}$
-- statement:
--   Let $n=2t+1$ and $1\le K\le n$. Fix a prefix immediately before two spreading rounds — a corrupted set of size at most $t$ and the holdings — and a predicate $\varphi$ on records fixed at the prefix. Suppose a set $A$ of at least $t+1$ identities are witnesses: every currently uncorrupted member of $A$ holds some record satisfying $\varphi$. If in each round every uncorrupted player performs $K$ trials carrying its full retained buffer, then for every adaptive continuation, every recipient uncorrupted through both rounds holds a record satisfying $\varphi$, except with probability at most
--
--   $$\delta_{fin}=e^{-K/128}+n\,e^{-K^2/(16n)}.$$
--
--   With $\varphi=(\cdot=P)$ this is Lemma 7.5 for a payload $P$; with a general $\varphi$ it is Corollary 7.6, used for termination evidence. One more witness than the remaining corruption budget is what makes recovery correct.
--
--   Differences from the source:
--
--   - generalization: Lemma 7.5 for one payload P and Corollary 7.6 for a predicate, two statements → one statement for a predicate φ on tokens; reason: φ = (· = P) is Lemma 7.5, and a predicate on encoded evidence is a predicate on tokens
--   - encoding: payload buffers of an execution → token holdings in the token game; reason: the lemma concerns possession only
--   - generalization: the adversary of §7.1 → an adversary that may add any token to any holding through a corrupted identity; reason: extra tokens only enlarge holdings and never change an honest trial count
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Lemma 7.5, p.24 (PDF p.25), eq. (15); Corollary 7.6, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_BeyondDS_TokenState
import Definitions.Def_BeyondDS_TrialStep

set_option autoImplicit false

open scoped ENNReal

namespace BeyondDS

/-- Lemma 7.5 (Two-round delivery from witnesses) with Corollary 7.6 (Delivery of evidence satisfying a predicate), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), pp.24–25 (PDF 25–26),
eq. (15): fix a prefix immediately before two spreading rounds and a predicate `φ` on records, fixed at the prefix. If at least `t + 1` identities are witnesses, each
currently uncorrupted witness holding some record with `φ`, and in each of the two rounds every uncorrupted player performs `K` trials carrying its full retained buffer,
then for `1 ≤ K ≤ n` every recipient uncorrupted through both rounds receives some satisfying record, except with probability at most
`δfin = exp(−K/128) + n exp(−K²/(16n))`. "The bound holds for every admissible adaptive continuation of the fixed prefix."

**Formalization Note.** Lemma 7.5 is the case `φ = (· = P)`. Stated on the token game; the prefix is the corrupted set, of size at most `t`, and the holdings. -/
theorem lemma_7_5 (t K : ℕ) {Token : Type} [DecidableEq Token] (A : TokenAdversary (2 * t + 1) Token) (a : A.σ)
    (C₀ : Finset (Fin (2 * t + 1))) (hC₀ : C₀.card ≤ t) (h : Fin (2 * t + 1) → Finset Token)
    (φ : Token → Prop) (Wit : Finset (Fin (2 * t + 1))) (hWit : t + 1 ≤ Wit.card)
    (hHold : ∀ i ∈ Wit, i ∉ C₀ → ∃ z ∈ h i, φ z) (hK₁ : 1 ≤ K) (hKn : K ≤ 2 * t + 1) :
    (tokenEpoch t K A (a, tokenStart C₀ h)).toOuterMeasure
        {y | ∃ r, y.2.UncorruptedThroughEpoch r ∧ ¬ ∃ z ∈ y.2.hold r, φ z} ≤
      ENNReal.ofReal (deltaFin (2 * t + 1) K) := by sorry

end BeyondDS
