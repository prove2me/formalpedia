-- Prove2me | Theorems.Thm_CosDensity_lemma_3_1
-- name    : CosDensity.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:10.569863+00:00
-- url     : https://prove2.me/theorems/9b4a430a-f95d-4406-8ff4-eb24c89655af
-- title:
--   Lemma 3.1 — one-way $\mathrm{INDEX}_N$ needs $\Omega(N)$ bits
-- statement:
--   There is an absolute constant $c>0$ such that, for every $N$, every public-coin one-way protocol for $\mathrm{INDEX}_N$ with a finite message set $M$ that errs with probability at most $1/3$ on every input pair uses
--
--   $$c\,N\le\log_2|M|$$
--
--   bits of communication.
--
--   This is the classical lower bound of Kremer, Nisan and Ron for the one-way randomized communication complexity of INDEX; the paper cites it and every streaming lower bound in §8 reduces to it.
--
--   Differences from the source:
--   - reading: every one-way protocol for INDEX_N with error at most 1/3 uses Ω(N) bits → ∃ c > 0 ∀ N, every public-coin protocol on an arbitrary probability space whose success sets contain measurable events of measure ≥ 2/3 has c·N ≤ log₂|M|; reason: public coins with an arbitrary seed space and the inner-measure success form are the strongest standard reading, and the form the reduction produces
--   - encoding: every protocol (seed space and message set of any kind) → seed space Ω and message set M in Lean's base universe Type; reason: Lean universe convention; every finite message set and every seed space the proof uses (Fin k, Fin N → Bool, measure spaces of ordinary mathematics) lives in Type
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §3, Lemma 3.1, p.13 (pdf_page 14), citing [KN96]

import Mathlib
import Definitions.Def_CosDensity_StreamAlg
import Definitions.Def_CosDensity_OneWayProtocol

open MeasureTheory

namespace CosDensity

/-- **Lemma 3.1** (INDEX lower bound, cited from [KN96]). Q. Zhang, *Frequency Moments Beyond
Equality: Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…),
§3, Lemma 3.1, p.13 (pdf_page 14).

Every one-way protocol for INDEX_N with error at most 1/3 uses `Ω(N)` bits of communication: there
is an absolute `c > 0` such that every public-coin one-way protocol with a finite message set `M`
that answers every input pair correctly with probability at least 2/3 has `c N ≤ log₂ |M|`.

**Formalization Note.** Protocols use public coins from an arbitrary probability space `(Ω, μ)`;
success is the inner-measure form `SolvesIndex`. The constant is chosen before `N`. -/
theorem lemma_3_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (Ω M : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] [Fintype M] (π : OneWayProtocol N Ω M),
      SolvesIndex μ π → c * N ≤ memoryBits M := by sorry

end CosDensity
