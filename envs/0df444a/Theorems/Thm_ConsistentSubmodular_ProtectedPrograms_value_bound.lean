-- Prove2me | Theorems.Thm_ConsistentSubmodular_ProtectedPrograms_value_bound
-- name    : ConsistentSubmodular.ProtectedPrograms.value_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:23.373133+00:00
-- url     : https://prove2.me/theorems/75349cda-3bdb-4941-9849-762b49c7ed6e
-- title:
--   Approximation guarantee of the selected set at every time
-- statement:
--   Let $f$ be an objective on $[n]$, $k,\kappa,b,\ell,R,B\in\mathbb N$ and $\beta,\eta,\gamma\in\mathbb R$. Let $C$ be a protected clock for the sequence $F(t)=\mathrm{OPT}_k(t):=f.\mathrm{prefixOptimum}\,k\,t$ (the best value of a set of at most $k$ elements among the first $t$ arrivals) with parameters $\eta,b,\ell$, and let $P$ be protected programs for $(f,\kappa,\beta,C,R,B)$. Assume $b>0$, $\eta\ge0$, $\gamma\le 3/4$, and the comparison property
--   $$\forall s,t:\quad \mathrm{OPT}_k(t)\le(1+\eta)\,\mathrm{OPT}_k(s)\ \Longrightarrow\ \gamma\,\mathrm{OPT}_k(t)\le\beta\,\mathrm{OPT}_\kappa(s).$$
--   Then for every time $t\in\mathbb N$,
--   $$\gamma\cdot\mathrm{OPT}_k(t)\ \le\ f\big(P.\mathrm{selected}(t)\big).$$
--
--   The local certificates of the programs, combined with the protection property of the clock (either the optimum is stable over an interval or has grown fourfold), give the approximation ratio at every actual time, including during unfinished transitions and on both sides of block boundaries.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/GlobalSchedule.lean#L93-L180 (`ConsistentSubmodular.ProtectedPrograms.value_bound`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_GlobalSchedule

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedPrograms
variable {n b ell κ k R B : ℕ} {f : Objective n} {β η γ : ℝ}
variable {C : ProtectedClock (f.prefixOptimum k) η b ell}
variable (P : ProtectedPrograms f κ β C R B)

theorem ConsistentSubmodular.ProtectedPrograms.value_bound (hb : 0 < b) (hη : 0 ≤ η) (hγ : γ ≤ (3 : ℝ) / 4)
    (compare : ∀ s t, f.prefixOptimum k t ≤ (1 + η) * f.prefixOptimum k s →
      γ * f.prefixOptimum k t ≤ β * f.prefixOptimum κ s) (t : ℕ) :
    γ * f.prefixOptimum k t ≤ f.value (P.selected t) := by sorry
