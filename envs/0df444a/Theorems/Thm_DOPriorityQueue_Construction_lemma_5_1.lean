-- Prove2me | Theorems.Thm_DOPriorityQueue_Construction_lemma_5_1
-- name    : DOPriorityQueue.Construction.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:04:14.828711+00:00
-- url     : https://prove2.me/theorems/c9e9ce1a-8bfc-4588-8cae-29521053f7a2
-- title:
--   Lemma 5.1 — Reflection and stability
-- statement:
--   Consider any event sequence of the stable priority queue (real calls and auxiliary events, Section 4.2), with $A_t(x)$ the number of original records inserted by event $t$ with key at most $x$, $N_t$ the number of extraction calls through event $t$ (including empty ones), and $Q_t(x)$ the number of currently live records with key at most $x$. Define $X_t(x)=A_t(x)-N_t$. Then for every event $t$ and threshold $x$,
--   $$Q_t(x)=X_t(x)-\min_{0\le u\le t}X_u(x).$$
--   Moreover, if an estimated process satisfies $|\hat A_t(x)-A_t(x)|\le E$ at every real and auxiliary event, and
--   $$\hat X_t(x)=\hat A_t(x)-N_t,\qquad \hat Q_t(x)=\hat X_t(x)-\min_{u\le t}\hat X_u(x),$$
--   then $|\hat Q_t(x)-Q_t(x)|\le 2E$ for all $t$ and $x$.
--
--   The identity expresses the live prefix count as a reflected insertion-minus-extraction process; the stability bound transfers the error of the historical summaries to the live-count estimate maintained by the segment tree, independently of the number of extractions.
--
--   Differences from the source:
--   - encoding: thresholds x in the encoded key universe [V] → thresholds x = (priority, call index) pairs in lexicographic order; reason: the fixed-width encoding of Section 2 is order preserving, so every integer threshold cuts the same key prefix as a pair threshold
--   - generalization: the event process of the core's history → every finite event sequence of the stable queue with arbitrary payloads and priorities, and every integer-valued estimate Â and integer E; reason: the core's event process is such a sequence (Section 4.2 events: calls and auxiliary replacements) and its estimates are integers, so the statement specializes to the source's
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), p. 21, Lemma 5.1

import Definitions.Def_DOPriorityQueue_Construction_EventProcess

set_option autoImplicit false

namespace DOPriorityQueue.Construction

/-- Guo--Hong--Li, STOC 2027 submission #538 (October 2026), p. 21, Lemma 5.1.
With `X_t(x) = A_t(x) - N_t`, the live prefix count is `Q_t(x) = X_t(x) - min_{u ≤ t} X_u(x)`;
and any estimate `Â` within `E` of `A` at every real and auxiliary event gives a
reflected estimate `Q̂` within `2E` of `Q`. Events are indexed `0, …, events.length`. -/
theorem lemma_5_1 {Ball : Type} (events : List (Event Ball)) :
    (∀ t ≤ events.length, ∀ x : ℕ × ℕ,
      (liveAtMost events t x : ℤ) =
        ((insertedAtMost events t x : ℤ) - extractionCount events t) -
          runningMin (fun u => (insertedAtMost events u x : ℤ) - extractionCount events u) t) ∧
    (∀ (Ahat : ℕ → ℕ × ℕ → ℤ) (E : ℤ),
      (∀ t ≤ events.length, ∀ x : ℕ × ℕ, |Ahat t x - insertedAtMost events t x| ≤ E) →
      ∀ t ≤ events.length, ∀ x : ℕ × ℕ,
        |((Ahat t x - extractionCount events t) -
            runningMin (fun u => Ahat u x - extractionCount events u) t) -
          (liveAtMost events t x : ℤ)| ≤ 2 * E) := by sorry

end DOPriorityQueue.Construction
