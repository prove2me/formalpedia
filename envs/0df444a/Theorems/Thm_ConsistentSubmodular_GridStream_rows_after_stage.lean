-- Prove2me | Theorems.Thm_ConsistentSubmodular_GridStream_rows_after_stage
-- name    : ConsistentSubmodular.GridStream.rows_after_stage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:35.733627+00:00
-- url     : https://prove2.me/theorems/f1e7ad61-c6ec-4aa1-973f-2c0270407d94
-- title:
--   Lemma 6, part 2 — few rows are held after stage $k$
-- statement:
--   Let $k>0$ and $m\ge k$, and consider the coverage stream $\Sigma$ with budget $k$ and $m$ stages, whose length is $N=k+mk$. Let $S_0,\dots,S_N$ be a feasible trajectory with cardinality budget $k$ and some recourse bound $C$ ($S_0=\emptyset$, $S_t\subseteq X_t$, $|S_t|\le k$, and $|S_{t+1}\triangle S_t|\le C$). Assume that it is a $\tfrac34$-approximation at every time: for every $t$ and every $A\subseteq X_t$ with $|A|\le k$,
--   $$\tfrac34\,\mathrm{cov}(A)\le\mathrm{cov}(S_t).$$
--   Let $n$ be the number of rows $a_1,\dots,a_k$ held by $S_t$ at the time $t=k+k^2=k(k+1)$, the end of stage $k$. Then
--   $$3\,n\le k,\qquad\text{i.e. } n\le k/3 .$$
--
--   Comparison with the competitor $B_k$, which covers $2k^2$ elements, gives $4n^2-8kn+2k^2\ge0$, that is $4\alpha^2-8\alpha+2\ge0$ for $\alpha=n/k\le1$, hence $\alpha\le1-\tfrac{\sqrt2}{2}\le\tfrac13$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Impossibility/GridStream.lean#L74-L111 (`ConsistentSubmodular.GridStream.rows_after_stage`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open Finset
open ConsistentSubmodular
variable {k m C : ℕ} {S : Fin (k + m * k + 1) → Finset (Fin (k + m * k))}

theorem ConsistentSubmodular.GridStream.rows_after_stage (hk : 0 < k) (hm : k ≤ m) (hS : FeasibleTrajectory k C S)
    (happrox : ∀ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
      A ⊆ arrivedPrefix (k + m * k) t.val → A.card ≤ k →
      3 / 4 * coverageValue (gridStreamCover k m) A ≤
        coverageValue (gridStreamCover k m) (S t)) :
    3 * rowsHeld k (S ⟨k + k * k, by
      have := Nat.mul_le_mul_right k hm
      omega⟩) ≤ k := by sorry
