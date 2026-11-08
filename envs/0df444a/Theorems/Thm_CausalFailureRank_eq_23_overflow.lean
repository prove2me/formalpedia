-- Prove2me | Theorems.Thm_CausalFailureRank_eq_23_overflow
-- name    : CausalFailureRank.eq_23_overflow
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:15:46.413372+00:00
-- url     : https://prove2.me/theorems/95ff87f2-0b73-495b-8d9f-ce7667a5a419
-- title:
--   Eq. (23) — overflow of the ideal SPRT
-- statement:
--   For $0<\delta\le1/2$, each stage $i$, each true state $x$ and each target $p\ge\delta/C_N$, under the i.i.d. tape of law $P_i^x$ the ideal SPRT fails to stop by the analytic quota $Q_i$ with probability at most $\delta/(2N)$.
--
--   Differences from the source:
--   - reading: "conditional on any entry history and true state" → the i.i.d. tape of the true state; reason: stage tapes are independent of the entry history, so this is the conditional law
--   - encoding: $\delta\to 0$ regime of a "risk" → $0<\delta\le1/2$ as hypothesis; reason: the range App. B.5 uses for its controller, $r=\delta/2\le 1/4$
--   - encoding: stages $1,\dots,N+1$ → 0-based stages, terminal $i\ge N$; reason: Lean indexing; no instance changes
--   - generalization: rational probabilities, fees and risk parameters → real ones; reason: rationality serves only computability, which is not claimed here; the rational case is an instance
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.5, eq. (23), p.18

import Mathlib
import Definitions.Def_CausalFailureRank_tapeLaw
import Definitions.Def_CausalFailureRank_J
import Definitions.Def_CausalFailureRank_Qanalytic

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- **Eq. (23): overflow.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.5, p.18: "failure of the ideal SPRT to stop by Q_i implies its
true-direction score is below b_max + L_i. Its mean is at least d_i Q_i, and its increment range has
length at most 2M_i. Hoeffding's bound and (23) yield overflow probability at most δ/(2N)."

**Formalization Note.** Under the i.i.d. tape of either true state `x`, for every target `p ≥ δ / C_N`; the
paper's "every tested posterior target is at least δ/C_N". `δ` is real, `0 < δ ≤ 1/2`. -/
theorem eq_23_overflow (I : Instance N q) (i : Fin N) (x : Bool) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (p : ℝ) (hp : δ / CN N ≤ p) :
    iidLaw I i x {tape | ((Qanalytic I δ i : ℕ) : ℕ∞) < stopTime (sprtRule I i p) tape} ≤
      ENNReal.ofReal (δ / (2 * N)) := by sorry

end CausalFailureRank
