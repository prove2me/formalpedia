-- Prove2me | Theorems.Thm_BeyondDS_lemma_7_4
-- name    : BeyondDS.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:05.604457+00:00
-- url     : https://prove2.me/theorems/705051b8-c4af-4780-9018-3d04be349b19
-- title:
--   Lemma 7.4 — a two-round epoch delivers all but $B$ frozen buffers, except with probability $\delta_{ep}$
-- statement:
--   Let $n=2t+1$, $1\le K\le n$, $B=\min\{n,\lceil512n/K\rceil\}$. At the start of a two-round epoch, from any corrupted set of size at most $t$, every uncorrupted source $i$ freezes a finite buffer $W_i$ and performs $K$ trials carrying it; in the second round every uncorrupted player performs $K$ trials carrying what it retained initially and received in the first round. Against every adaptive adversary, except with probability at most
--
--   $$\delta_{ep}=e^{-2n}+n^2e^{-K^2/(16n)},$$
--
--   there is a set $X$ of at most $B$ sources such that every source outside $X$ uncorrupted through the epoch has its whole buffer delivered to every recipient uncorrupted through the epoch. On every outcome, the epoch sends at most $2nK$ messages before their senders' corruptions.
--
--   The two epochs of each dissemination call make recovery cheap with high probability; this is where the message bound comes from.
--
--   **Formalization Note** Stated on the token game: buffers are finite sets of tokens.
--
--   Differences from the source:
--
--   - encoding: buffers of signed records in an execution → finite sets of tokens in the token game; reason: the lemma concerns possession only
--   - generalization: the adversary of §7.1, which can forward only records it holds → an adversary that may add any token to any holding through a corrupted identity; reason: extra tokens only enlarge holdings and never change an honest trial count, and the paper's adversary is a special case
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Lemma 7.4, p.24 (PDF p.25), eq. (14)

import Mathlib
import Definitions.Def_BeyondDS_TokenState
import Definitions.Def_BeyondDS_TrialStep

set_option autoImplicit false

open scoped ENNReal

namespace BeyondDS

/-- Lemma 7.4 (Two-round dissemination of buffers), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.24 (PDF 25), eq. (14): each uncorrupted source
freezes a finite buffer `W i` and performs `K` trials carrying it; in the second round every uncorrupted player performs `K` trials carrying what it
retained initially and received. Except with probability at most `δep = exp(−2n) + n² exp(−K²/(16n))`, all but at most `B` sources uncorrupted through
the epoch have their whole frozen buffers delivered to every recipient uncorrupted through the epoch. The epoch sends at most `2nK` messages before their
senders' corruptions, on every outcome.

**Formalization Note.** Stated on the token game: buffers are finite sets of tokens, as the lemma concerns possession only. The adversary sees every destination
and holding, corrupts between trials, and adds tokens through corrupted identities; the start is any corrupted set of size at most `t`. -/
theorem lemma_7_4 (t K : ℕ) {Token : Type} [DecidableEq Token] (A : TokenAdversary (2 * t + 1) Token) (a : A.σ)
    (C₀ : Finset (Fin (2 * t + 1))) (hC₀ : C₀.card ≤ t) (W : Fin (2 * t + 1) → Finset Token)
    (hK₁ : 1 ≤ K) (hKn : K ≤ 2 * t + 1) :
    (tokenEpoch t K A (a, tokenStart C₀ W)).toOuterMeasure
        {y | ¬ ∃ X : Finset (Fin (2 * t + 1)),
          X.card ≤ min (2 * t + 1) ⌈512 * ((2 * t + 1 : ℕ) : ℝ) / K⌉₊ ∧
          ∀ s, s ∉ X → y.2.UncorruptedThroughEpoch s → ∀ r, y.2.UncorruptedThroughEpoch r → W s ⊆ y.2.hold r} ≤
      ENNReal.ofReal (deltaEp (2 * t + 1) K) ∧
    ∀ y ∈ (tokenEpoch t K A (a, tokenStart C₀ W)).support, y.2.msgs ≤ 2 * (2 * t + 1) * K := by sorry

end BeyondDS
