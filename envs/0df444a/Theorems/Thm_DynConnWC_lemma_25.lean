-- Prove2me | Theorems.Thm_DynConnWC_lemma_25
-- name    : DynConnWC.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:41:43.217236+00:00
-- url     : https://prove2.me/theorems/ef2628c5-ba29-485f-bde4-9aadc4558677
-- title:
--   Lemma 25 — fixed-sequence correctness extends to adversaries that see only the answers
-- statement:
--   Let $Q$ be any program of the online randomized word RAM, $T_0\in\mathbb N$ and $\delta\in\mathbb R$. Suppose that for every valid operation sequence with at most $T_0$ updates, fixed in advance, all query answers are correct with probability at least $1-\delta$ over the tape. Then the same holds for an adversary that sees only the previous answers: if the sequence it issues against the exact oracle is valid with at most $T_0$ updates, then for every number $N$ of rounds, all answers it receives in the first $N$ rounds against $Q$ are correct with probability at least $1-\delta$.
--
--   Thus the correctness of the structure carries over from fixed sequences to adaptive ones.
--
--   Differences from the source:
--   - generalization: the data structure of the paper → any program of the machine; reason: the proof uses only that the run is online and deterministic once the tape is fixed
--   - reading: an adversary with its own random choices, issuing only valid operations and at most $T_0$ updates → deterministic strategies, with validity and the update count required only of the run against the exact oracle; reason: the source's proof fixes the randomness, averages, and applies the condition to that run; a uniform bound over deterministic strategies covers mixtures
--   - encoding: any number of queries → every finite number $N$ of rounds, with the bound uniform in $N$; reason: by continuity of measure this is equivalent to the infinite run
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Lemma 25, p.24 (PDF 25–26)

import Mathlib
import Definitions.Def_DynConnWC_Bounds

set_option autoImplicit false

namespace DynConnWC

open MeasureTheory in
/-- **Lemma 25 (Adaptive updates).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.24 (PDF 25–26).
"Suppose that, for every sequence of at most T0 updates, fixed in advance and interleaved with any
number of queries, all query answers are correct with probability at least 1 − δ. Then the same holds
when the sequence is chosen by an adversary that sees only the previous query answers."

**Formalization Note.** For any program. The adversary is a deterministic strategy; one with its own
randomness is a mixture of these, and the proof on p.25 averages over it. The hypothesis on the
adversary is the one the proof uses: the sequence it issues against the exact oracle is valid with at
most `T0` updates, in every number of rounds. "Any number of queries" is the bound for every number `N`
of rounds. -/
theorem lemma_25 {n : ℕ} (W : ℕ) (Q : Program) (T0 : ℕ) (δ : ℝ)
    (hfixed : ∀ σ : List (Op n), Valid σ → numUpdates σ ≤ T0 →
      ENNReal.ofReal (1 - δ) ≤ tapeLaw W {ω | AllCorrect W Q n ω σ})
    (A : Adversary n)
    (hA : ∀ N, Valid (oracleOps A N) ∧ numUpdates (oracleOps A N) ≤ T0) (N : ℕ) :
    ENNReal.ofReal (1 - δ) ≤ tapeLaw W {ω | AdvAllCorrect W Q A N ω} := by sorry

end DynConnWC
