-- Prove2me | Theorems.Thm_BoolCSPDel_index_average
-- name    : BoolCSPDel.index_average
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:53:13.239123+00:00
-- url     : https://prove2.me/theorems/72ee924f-54e1-4c5c-b8b4-9500966baa67
-- title:
--   INDEX with average error $1/3$ needs $\Omega(N)$ bits
-- statement:
--   In one-way INDEX on $N$ bits, Alice holds $z\in\{0,1\}^N$, Bob holds $q\in[N]$, they share a public seed, and Alice sends one message from a finite set $M$. If Bob outputs $z_q$ with probability at least $2/3$ on average over uniform independent $z$ and $q$, then
--
--   $$\log_2|M|\ge cN$$
--
--   for an absolute $c>0$.
--
--   Theorem 4.2 reduces from this form. The worst-case form, Open on the platform as `CosDensity.lemma_3_1`, follows from it.
--
--   **Formalization Note** Success is measured by measurable events inside the success sets, in the style of `CosDensity.SucceedsWP`.
--
--   Differences from the source:
--   - encoding: average error at most 1/3 → measurable events A z q inside the success sets, of average measure at least 2/3; reason: an inner-measure form of the average; for measurable success sets it is the same
--   - encoding: Ω(N) one-way communication → c N ≤ log₂|M|, with c absolute; reason: a message from a finite set M; the page charges its encoding length
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), proof of Theorem 4.2, p.28; p.11

import Mathlib
import Definitions.Def_CosDensity_OneWayProtocol

open MeasureTheory

namespace BoolCSPDel

/-- **INDEX under uniform inputs.** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), proof of Theorem 4.2, p.28: "a sketch with average error at
most 1/3 on this distribution yields a public-coin INDEX protocol with the same error … The `Ω(n^k)`
one-way communication lower bound"; p.11, "Even with shared randomness and constant error probability
bounded away from 1/2".

A public-coin one-way protocol for `INDEX_N` with average error at most `1/3` over uniform independent
`z` and `q` has a message set of at least `cN` bits.

**Formalization Note.** Success is an inner-measure bound in the style of `CosDensity.SucceedsWP`:
measurable events inside the success sets, of average measure at least `2/3`. -/
theorem index_average : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), 1 ≤ N →
    ∀ (Ω M : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] [Fintype M]
      (π : CosDensity.OneWayProtocol N Ω M) (A : (Fin N → Bool) → Fin N → Set Ω),
      (∀ z q, MeasurableSet (A z q)) →
      (∀ z q, A z q ⊆ {ω | π.dec ω (π.msg ω z) q = z q}) →
      (2 / 3 : ENNReal) * ((2 : ENNReal) ^ N * N) ≤ ∑ z, ∑ q, μ (A z q) →
      c * N ≤ CosDensity.memoryBits M := by sorry

end BoolCSPDel
