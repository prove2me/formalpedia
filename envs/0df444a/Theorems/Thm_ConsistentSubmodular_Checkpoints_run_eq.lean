-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_run_eq
-- name    : ConsistentSubmodular.Checkpoints.run_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:09.258687+00:00
-- url     : https://prove2.me/theorems/c425bbc9-aed1-4feb-a2a6-0bfcaa197668
-- title:
--   Algorithm 1 at time $u$ equals the state after $u \bmod \ell$ updates of block $\lfloor u/\ell\rfloor$
-- statement:
--   Let $P=(\ell,\kappa,h,s)$ be parameters of Algorithm 1 that are valid for the budget $k$ (that is, $\ell>0$, $h>0$, $\kappa+2\ell\le k$ and $k\le s\lfloor \ell/h\rfloor$). Let $(A_i)_{i\ge0}$ be checkpoint samples and $(\sigma_i)_{i\ge0}$ subblock choices that are good: for every $i$, $\sigma_i<h$, $A_i\subseteq X_{i\ell}$ and $|A_i|\le\kappa$. Let $\mathrm{state}(i,r)$ denote the set held after $r$ updates of block $i$, and $\mathrm{ALG}_u$ the set maintained by the algorithm at time $u$. Then for every $u\in\mathbb N$,
--   $$\mathrm{ALG}_u=\mathrm{state}\bigl(\lfloor u/\ell\rfloor,\; u \bmod \ell\bigr).$$
--
--   The algorithm is defined through the block $\lfloor (t-1)/\ell\rfloor$ and a position in $\{1,\dots,\ell\}$ for $t\ge1$. This identity rewrites it with the position $u\bmod\ell\in\{0,\dots,\ell-1\}$, so that the end of a block coincides with the start of the next one: the transition into the next core has finished by then. It is the form used in the feasibility and value analysis of Algorithm 1.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointAlgorithm.lean#L225-L261 (`ConsistentSubmodular.Checkpoints.run_eq`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointAlgorithm

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}
variable {P : Params} {A : ℕ → Finset (Fin n)} {σ : ℕ → ℕ} {k : ℕ}

theorem ConsistentSubmodular.Checkpoints.run_eq (hP : P.Valid k) (hg : Good P A σ) (u : ℕ) :
    run P A σ u = state P A σ (u / P.ℓ) (u % P.ℓ) := by sorry
