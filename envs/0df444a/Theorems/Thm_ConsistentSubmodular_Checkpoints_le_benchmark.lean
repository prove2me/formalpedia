-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_le_benchmark
-- name    : ConsistentSubmodular.Checkpoints.le_benchmark
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:37.497209+00:00
-- url     : https://prove2.me/theorems/4b54a1ce-f6e9-48e7-b789-2ca1c28e2e08
-- title:
--   Checkpoint benchmark dominates every small set arrived by time $c+j$
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on a stream of $n$ elements $x_1,\dots,x_n$, let $\kappa, c\in\mathbb N$, and let $W$ be the checkpoint instance at time $c$: present elements $X_c=\{x_1,\dots,x_c\}$, core budget $\kappa$, stages $j=0,\dots,n-c$, future prefixes $R_j=\{x_{c+1},\dots,x_{c+j}\}$, and candidates $O_j\subseteq X_c$ with $|O_j|\le\kappa$ maximizing $f(O\cup R_j)$. Let $j$ be a stage and let $T\subseteq X_{c+j}$ with $|T|\le\kappa$. Then
--   $$f(T)\le f(O_j\cup R_j),$$
--   that is, $f(T)$ is at most the benchmark of $W$ at stage $j$.
--
--   This bound compares any feasible set of size at most $\kappa$ that has arrived by time $c+j$ with the benchmark of the checkpoint instance. It is what allows the addition-robust guarantee at a checkpoint to be turned into a guarantee against every competitor $T$ in the reduction of Lemma 1.
--
--   **Formalization Note** The stage $j$ is an element of `Fin (lastStage + 1)` with `lastStage = n - c`, and `arrivedPrefix n (c + j.val)` is $X_{c+j}$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointWindow.lean#L232-L249 (`ConsistentSubmodular.Checkpoints.le_benchmark`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointWindow

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}

theorem ConsistentSubmodular.Checkpoints.le_benchmark (f : Objective n) (κ c : ℕ) (j : Fin ((window f κ c).lastStage + 1))
    {T : Finset (Fin n)} (hT : T ⊆ arrivedPrefix n (c + j.val)) (hcard : T.card ≤ κ) :
    f.value T ≤ (window f κ c).benchmark j := by sorry
