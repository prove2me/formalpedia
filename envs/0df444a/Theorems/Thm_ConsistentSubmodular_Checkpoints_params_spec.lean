-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_params_spec
-- name    : ConsistentSubmodular.Checkpoints.params_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:28.701933+00:00
-- url     : https://prove2.me/theorems/89e1f5d6-6321-4063-af3c-3aa73d5f3f69
-- title:
--   Parameter estimates of Algorithm 1 for $k\ge 8\gamma^{-2}$
-- statement:
--   Let $0<\gamma<1/8$ and let $k\in\mathbb N$ with $k\ge 8/\gamma^2$. Let the parameters of Algorithm 1 be $\ell=\lfloor\gamma k\rfloor$, $\kappa=k-2\ell$, $h=\lceil 1/\gamma\rceil$, and $s=\lfloor k/\lfloor \ell/h\rfloor\rfloor+1$. Then:
--
--   1. the parameters are valid for the budget $k$: $\ell>0$, $h>0$, $\kappa+2\ell\le k$, and $k\le s\lfloor \ell/h\rfloor$;
--   2. $2s+1\le \lceil 16/\gamma^2\rceil+3$, the consistency bound of Lemma 1;
--   3. $1/h\le\gamma$;
--   4. $1-2\gamma\le \kappa/k$.
--
--   These are the numerical estimates of the proof of Lemma 1: the shortest subblock has $\lfloor \ell/h\rfloor\ge\gamma^2k/8$ updates, so $s$ transition operations per update suffice and the number of changes per update is $O(\gamma^{-2})$; the probability $1/h$ of being inside the selected subblock is at most $\gamma$, and the core budget $\kappa$ loses only a factor $1-2\gamma$ relative to $k$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/Checkpoints.lean#L52-L135 (`ConsistentSubmodular.Checkpoints.params_spec`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_Checkpoints

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints

theorem ConsistentSubmodular.Checkpoints.params_spec {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) {k : ℕ}
    (hk : 8 / γ ^ 2 ≤ k) :
    (params γ k).Valid k ∧ 2 * (params γ k).s + 1 ≤ consistency γ ∧
      1 / ((params γ k).h : ℝ) ≤ γ ∧ 1 - 2 * γ ≤ ((params γ k).κ : ℝ) / k := by sorry
