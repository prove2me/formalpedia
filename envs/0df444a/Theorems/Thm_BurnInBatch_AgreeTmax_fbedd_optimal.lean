-- Prove2me | Theorems.Thm_BurnInBatch_AgreeTmax_fbedd_optimal
-- name    : BurnInBatch.AgreeTmax.fbedd_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:29:59.09692+00:00
-- url     : https://prove2.me/theorems/3010cb3d-4bdd-48b7-8a58-aabe3ed8849d
-- title:
--   FBEDD optimally solves $1/p_i=p,B/T_{\max}$
-- statement:
--   Consider $n$ jobs on a single batch processing machine of capacity $B\ge 1$, all available at time $0$, every job with the same processing time $p$, and due dates indexed so that $d_1\le d_2\le\dots\le d_n$. Let $S_{\mathrm{FBEDD}}$ be the Full-Batch EDD schedule: batches $\{1,\dots,B\}$, $\{B+1,\dots,2B\}$, $\dots$, processed in this order. Then $S_{\mathrm{FBEDD}}$ is a valid batch schedule of all jobs, and for every valid batch schedule $S$ of all jobs,
--   $$T_{\max}(S_{\mathrm{FBEDD}})\le T_{\max}(S).$$
--
--   With equal processing times every batch takes time $p$, so the result says that filling batches in due-date order is optimal for maximum tardiness.
--
--   **Formalization Note** The common processing time is $c\in\mathbb N$ (any value, $0$ included). $T_{\max}$ is $\max_i \max\{0, C_i-d_i\}$, computed with truncated subtraction in $\mathbb N$.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 769, Algorithm FBEDD and the sentence preceding it

import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model
import Definitions.Def_BurnInBatch_AgreeTmax_FBEDD

namespace BurnInBatch.AgreeTmax

/-- Algorithm FBEDD optimally solves `1/p_i = p, B/T_max` (Lee, Uzsoy & Martin-Vega 1992,
p. 769): if every job has processing time `c` and the jobs are indexed in nondecreasing order of
due dates, the full-batch EDD schedule is a valid batch schedule of all jobs, and its maximum
tardiness is at most that of every valid batch schedule of all jobs. -/
theorem fbedd_optimal {n B : ℕ} (hB : 0 < B) (c : ℕ) (d : Fin n → ℕ) (hd : Monotone d) :
    IsValid B Finset.univ (fbedd n B) ∧
      ∀ S : List (Finset (Fin n)), IsValid B Finset.univ S →
        Tmax (fun _ => c) d (fbedd n B) ≤ Tmax (fun _ => c) d S := by sorry

end BurnInBatch.AgreeTmax
