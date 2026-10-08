-- Prove2me | Theorems.Thm_BurnInBatch_TardyJobs_lemma_4
-- name    : BurnInBatch.TardyJobs.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:10.866981+00:00
-- url     : https://prove2.me/theorems/74030ce4-4498-4788-a0c5-b550cdfb9e49
-- title:
--   Lemma 4 — an optimal schedule has on-time batches first in batch-EDD order
-- statement:
--   Consider one batch machine of capacity $B\ge1$, common job processing time $p$, releases $r_j$, and due dates $d_j$. Suppose $r_i<r_j$ implies $d_i\le d_j$. There is an optimal complete schedule consisting of an initial list $A$ of batches whose every job is on time, followed by a list $T$ of batches whose every job is tardy; the batches in $A$ are in batch-EDD order. Thus, with $S=A\mathbin{+\!+}T$,
--
--   $$
--   U(S)=U^*,\qquad (j\in A\Rightarrow C_j(S)\le d_j),\qquad (j\in T\Rightarrow d_j<C_j(S)).
--   $$
--
--   This structural result lets subsequent statements place all tardy jobs after the on-time part while retaining the global optimum over complete schedules.
--
--   **Formalization Note** The strict-release form of agreeability permits unequal due dates when releases tie. $A$ and $T$ are lists of batches, and `Optimal` still ranges over every valid complete schedule.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 770, Lemma 4

import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model

namespace BurnInBatch.TardyJobs

/-- Lemma 4, p. 770: an optimal schedule can put every on-time batch first,
with those batches in batch-EDD order, and all tardy jobs afterward. -/
theorem lemma_4 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hB : 0 < B) (hagree : ∀ i j : Fin n, r i < r j → d i ≤ d j) :
    ∃ A T : List (Finset (Fin n)),
      Optimal B (equalTime p) r d (A ++ T) ∧
      (∀ P ∈ A, ∀ j ∈ P, jobCompletion (equalTime p) r (A ++ T) j ≤ d j) ∧
      (∀ P ∈ T, ∀ j ∈ P, d j < jobCompletion (equalTime p) r (A ++ T) j) ∧
      BatchEDD d A := by sorry

end BurnInBatch.TardyJobs
