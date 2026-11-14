-- Prove2me | Theorems.Thm_ConsistentSubmodular_ProtectedPrograms_trajectory_spec
-- name    : ConsistentSubmodular.ProtectedPrograms.trajectory_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:59.746209+00:00
-- url     : https://prove2.me/theorems/08d5c06b-a1e1-416b-a6cb-ab26e187db06
-- title:
--   Protected programs yield a feasible trajectory with fractional approximation
-- statement:
--   Let $f$ be an objective on $[n]$, $N,H,k,R\in\mathbb N$, $\alpha\in\mathbb R$, $p$ transfer parameters for $(N,H,k)$ (core size $p.\mathrm{core}$, block length $b=p.\mathrm{block}$, interval $\ell=p.\mathrm{interval}$, etc.), $C$ a protected clock for $\mathrm{OPT}_k(t)=f.\mathrm{prefixOptimum}\,k\,t$ with $\eta=1/N$, and $P$ protected programs for $(f,p.\mathrm{core},\alpha-2/N,C,R,p.\mathrm{core}+p.\mathrm{block}+H)$. Assume $k>0$, $\alpha\le3/4$ and $\alpha-14/N\ge0$. Then
--
--   1. the trajectory $t\mapsto P.\mathrm{selected}(t)$, $t=0,\dots,n$, is a feasible trajectory with cardinality budget $k$ and recourse budget $R+2$: it starts empty, $S_t\subseteq X_t$, $|S_t|\le k$ and $|S_{t+1}\triangle S_t|\le R+2$;
--   2. for every $t\in\{0,\dots,n\}$ and every $A\subseteq X_t$ with $|A|\le k$,
--   $$\Big(\alpha-\frac{14}{N}\Big)f(A)\ \le\ f\big(P.\mathrm{selected}(t)\big).$$
--
--   A family of rounded local programs thus produces a valid finite trajectory with one uniform per-update rate $R+2$ and the required fractional approximation.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/StreamingComparison.lean#L50-L70 (`ConsistentSubmodular.ProtectedPrograms.trajectory_spec`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_GlobalSchedule
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_StreamingParameters

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedPrograms
variable {n N H k R : ℕ} {f : Objective n} {α : ℝ}
variable (p : TransferParameters N H k)
variable {C : ProtectedClock (f.prefixOptimum k) ((1 : ℝ) / N) p.block p.interval}
variable (P : ProtectedPrograms f p.core (α - 2 * ((1 : ℝ) / N)) C R
  (p.core + p.block + H))

theorem ConsistentSubmodular.ProtectedPrograms.trajectory_spec (hk : 0 < k) (hα : α ≤ 3 / 4)
    (hγ : 0 ≤ α - 14 * ((1 : ℝ) / N)) :
    FeasibleTrajectory k (R + 2) (fun t : Fin (n + 1) => P.selected t.val) ∧
      ∀ (t : Fin (n + 1)) (A : Finset (Fin n)),
        A ⊆ arrivedPrefix n t.val → A.card ≤ k →
        (α - 14 * ((1 : ℝ) / N)) * f.value A ≤ f.value (P.selected t.val) := by sorry
