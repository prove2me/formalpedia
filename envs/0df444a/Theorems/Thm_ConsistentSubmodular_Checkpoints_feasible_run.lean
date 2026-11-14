-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_feasible_run
-- name    : ConsistentSubmodular.Checkpoints.feasible_run
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:40.756263+00:00
-- url     : https://prove2.me/theorems/8d2a98b5-2e9e-43f9-9a53-93229501dcec
-- title:
--   Algorithm 1 is a feasible trajectory with at most $2s+1$ changes per update
-- statement:
--   Let $P=(\ell,\kappa,h,s)$ be parameters valid for the budget $k$, and let checkpoint samples $(A_i)$ and subblock choices $(\sigma_i)$ be good (each $\sigma_i<h$, $A_i\subseteq X_{i\ell}$, $|A_i|\le\kappa$). Let $\mathrm{ALG}_t$ be the set maintained by Algorithm 1 at time $t$, for $t=0,\dots,n$. Then the trajectory $(\mathrm{ALG}_t)_{0\le t\le n}$ is feasible with cardinality budget $k$ and change budget $2s+1$:
--
--   1. $\mathrm{ALG}_0=\emptyset$;
--   2. for every $t$, $\mathrm{ALG}_t\subseteq X_t$ and $|\mathrm{ALG}_t|\le k$;
--   3. for every $t\in\{1,\dots,n\}$, $|\mathrm{ALG}_t\,\triangle\,\mathrm{ALG}_{t-1}|\le 2s+1$.
--
--   Thus every realization of the random choices yields an algorithm that is a legitimate consistent clairvoyant algorithm. This is the feasibility part of the analysis of Algorithm 1 in the proof of Lemma 1.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointAlgorithm.lean#L263-L282 (`ConsistentSubmodular.Checkpoints.feasible_run`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointAlgorithm

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}
variable {P : Params} {A : ℕ → Finset (Fin n)} {σ : ℕ → ℕ} {k : ℕ}

theorem ConsistentSubmodular.Checkpoints.feasible_run (hP : P.Valid k) (hg : Good P A σ) :
    FeasibleTrajectory k (2 * P.s + 1) (fun t : Fin (n + 1) => run P A σ t.val) := by sorry
