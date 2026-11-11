-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_theorem_2_1
-- name    : ConstrainedCorrelationRepulsion.Main.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:21.887774+00:00
-- url     : https://prove2.me/theorems/cfbdaa0a-47b6-475b-a5ec-8bfc8ce56218
-- title:
--   Theorem 2.1 — true-twin preservation in partitions and both LPs
-- statement:
--   Let $I$ be feasible, with arbitrary real separation and joining costs $w^+,w^-$. Let $u\ne v$ be non-hard, with $w^+_{uv}>w^-_{uv}$. For every other vertex $t$, require identical must-link incidence, identical cannot-link incidence, and equality of external differences $w^+_{ut}-w^-_{ut}=w^+_{vt}-w^-_{vt}$. Every optimal feasible partition joins $u,v$, and every optimal solution of each of the metric LP and the full cluster LP satisfies
--
--   $$
--   x_{uv}=0.
--   $$
--
--   The conclusion is universal over optima of all three problems, and does not require nonnegative pair costs or equality of the two individual external costs.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - encoding: pair costs defined only for distinct vertices → total functions on Sym2 with unused diagonal padding; probability padding lies in [0,1]; reason: every source assignment extends to such a function, every objective ignores the diagonal, and no source instance is excluded
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Theorem 2.1, printed p.14 (PDF p.15)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Instance

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem theorem_2_1 {n : ℕ} (I : Instance n) (w : PairCosts n)
    (hI : FeasibleInput I) (u v : Fin n) (hne : u ≠ v)
    (hcost : w.together s(u,v) < w.separate s(u,v))
    (hH : ¬ I.cannotLink.Adj u v)
    (htwins : ∀ t, t ≠ u → t ≠ v →
      (I.mustLink.Adj u t ↔ I.mustLink.Adj v t) ∧
      (I.cannotLink.Adj u t ↔ I.cannotLink.Adj v t) ∧
      w.separate s(u,t) - w.together s(u,t) = w.separate s(v,t) - w.together s(v,t)) :
  (∀ P, WeightedOptimal I w P → P u = P v) ∧
  (∀ x, MetricOptimal I w x → x u v = 0) ∧
  (∀ lam x, ClusterOptimal I w lam x → x u v = 0) := by sorry

end ConstrainedCorrelationRepulsion.Main
