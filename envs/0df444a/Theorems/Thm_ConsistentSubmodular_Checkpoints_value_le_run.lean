-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_value_le_run
-- name    : ConsistentSubmodular.Checkpoints.value_le_run
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:57.497558+00:00
-- url     : https://prove2.me/theorems/4001abd6-249d-4cd1-bef8-292720543943
-- title:
--   Algorithm 1 holds a full core outside the selected subblock
-- statement:
--   Let $P=(\ell,\kappa,h,s)$ be parameters valid for the budget $k$, let the samples $(A_i)$ and choices $(\sigma_i)$ be good, and let $f$ be a nonnegative monotone submodular objective. Fix a time $u$, write $i=\lfloor u/\ell\rfloor$ and $r=u\bmod \ell$, and let $F=\{x_{i\ell+1},\dots,x_{i\ell+r+1}\}$ be the arrivals of block $i$ up to time $u+1$. Let $C_i=A_{i-1}\cup B_i$ (and $C_0=\emptyset$) be the old core, where $B_i$ is the previous block, and let $\mathrm{lo}$, $\mathrm{hi}$ be the boundaries of subblock $\sigma_i$, whose updates are $\mathrm{lo}+1,\dots,\mathrm{hi}$. Then
--   $$\mathbf 1[r+1\le \mathrm{lo}]\; f(C_i\cup F)\;+\;\mathbf 1[r+1>\mathrm{lo}\ \wedge\ \mathrm{hi}\le r+1]\; f(A_i\cup F)\;\le\; f(\mathrm{ALG}_{u+1}).$$
--
--   So before the selected subblock the algorithm holds a superset of the old core together with the current arrivals, and after it a superset of the new core $A_i$ together with them; the two cases are exclusive, and the term of the other case is $0$. This is the value bound that is combined with the addition-robust guarantee of the corresponding checkpoint in the proof of Lemma 1.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointAlgorithm.lean#L284-L304 (`ConsistentSubmodular.Checkpoints.value_le_run`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointAlgorithm

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}
variable {P : Params} {A : ℕ → Finset (Fin n)} {σ : ℕ → ℕ} {k : ℕ}

theorem ConsistentSubmodular.Checkpoints.value_le_run (hP : P.Valid k) (hg : Good P A σ) (f : Objective n) (u : ℕ) :
    (if u % P.ℓ + 1 ≤ lo P.ℓ P.h (σ (u / P.ℓ)) then
        f.value (oldCore n P.ℓ A (u / P.ℓ) ∪ future n (u / P.ℓ * P.ℓ) (u % P.ℓ + 1)) else 0) +
      (if ¬ u % P.ℓ + 1 ≤ lo P.ℓ P.h (σ (u / P.ℓ)) ∧
          hi P.ℓ P.h (σ (u / P.ℓ)) ≤ u % P.ℓ + 1 then
        f.value (A (u / P.ℓ) ∪ future n (u / P.ℓ * P.ℓ) (u % P.ℓ + 1)) else 0) ≤
      f.value (run P A σ (u + 1)) := by sorry
