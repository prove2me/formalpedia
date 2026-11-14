-- Prove2me | Theorems.Thm_ConsistentSubmodular_GridStream_exists_bad_time
-- name    : ConsistentSubmodular.GridStream.exists_bad_time
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:43.605827+00:00
-- url     : https://prove2.me/theorems/e0584166-6341-402b-8630-e75ca46c63c2
-- title:
--   Theorem 3 (Appendix B.1) — a time of bad approximation on $\Sigma$
-- statement:
--   Let $k>0$ and $m\ge k$, and consider the coverage stream $\Sigma$ with budget $k$ and $m$ stages (length $N=k+mk$). Let $\varepsilon\in\mathbb R$ with $\varepsilon\ge 1/k$, and let $S_0,\dots,S_N$ be a feasible trajectory with cardinality budget $k$ and recourse bound $\lfloor\varepsilon k\rfloor$ ($S_0=\emptyset$, $S_t\subseteq X_t$, $|S_t|\le k$, $|S_{t+1}\triangle S_t|\le\lfloor\varepsilon k\rfloor$). Then there exist a time $t\in\{0,\dots,N\}$ and a set $A\subseteq X_t$ with $|A|\le k$ and $\mathrm{cov}(A)>0$ such that
--   $$\mathrm{cov}(S_t)\;\le\;\Bigl(\tfrac34+6\varepsilon\Bigr)\,\mathrm{cov}(A).$$
--
--   So every trajectory with recourse $\lfloor\varepsilon k\rfloor$ has a time at which it covers at most $\tfrac34+6\varepsilon$ times what a competitor covers. This is the impossibility argument showing that deterministic algorithms cannot beat the ratio $3/4$ with constant recourse.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Impossibility/GridStream.lean#L155-L275 (`ConsistentSubmodular.GridStream.exists_bad_time`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open Finset
open ConsistentSubmodular

theorem ConsistentSubmodular.GridStream.exists_bad_time {k m : ℕ} {ε : ℝ} (hk : 0 < k) (hm : k ≤ m)
    (hεk : 1 / (k : ℝ) ≤ ε) (S : Fin (k + m * k + 1) → Finset (Fin (k + m * k)))
    (hS : FeasibleTrajectory k ⌊ε * k⌋₊ S) :
    ∃ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
      A ⊆ arrivedPrefix (k + m * k) t.val ∧ A.card ≤ k ∧
      0 < coverageValue (gridStreamCover k m) A ∧
      coverageValue (gridStreamCover k m) (S t) ≤
        (3 / 4 + 6 * ε) * coverageValue (gridStreamCover k m) A := by sorry
