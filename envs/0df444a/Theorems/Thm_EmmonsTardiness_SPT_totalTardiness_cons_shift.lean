-- Prove2me | Theorems.Thm_EmmonsTardiness_SPT_totalTardiness_cons_shift
-- name    : EmmonsTardiness.SPT.totalTardiness_cons_shift
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:30:38.657342+00:00
-- url     : https://prove2.me/theorems/c25bd689-ab6e-4ec1-bd42-6653a78565c4
-- title:
--   p. 705 — processing J_k first re-references time to p_k and due dates to d_i − p_k
-- statement:
--   Let $J$ be a finite set of jobs with processing times $p_i$ and due dates $d_i$, let $J_k\in J$, and let $l'$ be a schedule of the remaining jobs $J\setminus\{J_k\}$. Write $k\,l'$ for the schedule of $J$ that processes $J_k$ first and then the jobs of $l'$ in order. Then
--   $$T_{p,d}(k\,l') = \max(0,\ p_k - d_k) + T_{p,d'}(l'),\qquad d'_i = d_i - p_k,$$
--   where $T_{p,d}$ is total tardiness over $J$ with due dates $d$, and $T_{p,d'}$ is total tardiness over $J\setminus\{J_k\}$ with the shifted due dates $d'$.
--
--   In words: once $J_k$ is processed first, the rest is the same problem on $n-1$ jobs with the time scale restarted at $p_k$, which "merely means setting $d_i$ to $d_i - p_k$". Some shifted due dates may be negative.
--
--   **Formalization Note** No hypothesis on the signs of $p$ or $d$ is needed.
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, https://doi.org/10.1287/opre.17.4.701, p. 705, paragraph after Corollary 1.3 (removing a job processed first)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

namespace EmmonsTardiness.SPT

open MooreLateJobs

/-- Emmons 1969, p. 705, paragraph after Corollary 1.3 (time re-referencing): if job `k` is
processed first and the remaining jobs `J ∖ {k}` follow in the order `l'`, the total tardiness
equals the tardiness `max(0, p_k − d_k)` of `k` plus the total tardiness of `l'` for the
remaining jobs measured from time `p_k`, i.e. with due dates `d_i − p_k`. -/
theorem totalTardiness_cons_shift {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (J : Finset ι)
    (k : ι) (hk : k ∈ J) (l' : List ι) (hl' : Shared.IsSchedule (J.erase k) l') :
    totalTardiness p d J (k :: l') =
      max 0 (p k - d k) + totalTardiness p (fun i => d i - p k) (J.erase k) l' := by sorry

end EmmonsTardiness.SPT
