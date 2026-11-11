-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_lemma_5_5
-- name    : ConstrainedDirSep.STSep.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:07:44.251421+00:00
-- url     : https://prove2.me/theorems/25b5322f-c4e9-4060-8e41-37d7802e362a
-- title:
--   Lemma 5.5 — replacing infinite arcs by k + 1 unit copies preserves cuts and minimum cut values ≤ k
-- statement:
--   Let $G'$ be a finite directed multigraph with arc capacities in $\{1,+\infty\}$, vertices $s,t$, $k\ge0$, and let $H$ replace every infinite-capacity arc by $k+1$ parallel capacity-one copies. Then:
--
--   1. a set of capacity-one arcs of $G'$ is an $s$–$t$ cut of $G'$ if and only if it is an $s$–$t$ cut of $H$;
--   2. the minimum $s$–$t$ cut values of $G'$ and $H$ agree whenever one of them is at most $k$;
--   3. every minimum $s$–$t$ cut of $H$ of value at most $k$ consists entirely of capacity-one arcs of $G'$.
--
--   This justifies working in the capacity-one multigraph $H$ inside each flow-augmentation branch.
--
--   Differences from the source:
--   - encoding: multigraph with capacities → arcs an indexed finite family with an infinite-capacity flag; H's arcs are the copies (a, i), i ∈ {0, …, k}, of infinite arcs and the single copy (a, 0) of capacity-one arcs; cut values in ℕ ∪ {∞}; reason: Lean convention; same instances.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 20 (PDF 23), Lemma 5.5 (proof p. 43, PDF 46)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Multigraph

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 20 (PDF 23), Lemma 5.5: let `H` replace every infinite-capacity arc of `G′`
by `k + 1` parallel capacity-one copies. A set of capacity-one arcs of `G′` is an s–t cut of `G′`
iff it is one of `H`; the minimum s–t cut values of `G′` and `H` agree whenever one is at most `k`;
and every minimum s–t cut of `H` of value at most `k` consists of capacity-one arcs of `G′`. -/
theorem lemma_5_5 {V A : Type*} [Fintype A] (G : CapMultigraph V A) (s t : V) (k : ℕ) :
    (∀ Z : Set A, (∀ a ∈ Z, G.inf a = false) →
      (G.toMultigraph.IsArcCut s t Z ↔
        (G.expand k).toMultigraph.IsArcCut s t (G.unitArc k '' Z))) ∧
    ((G.minCutValue s t ≤ (k : ℕ∞) ∨ (G.expand k).minCutValue s t ≤ (k : ℕ∞)) →
      G.minCutValue s t = (G.expand k).minCutValue s t) ∧
    ∀ Z : Finset (ExpArc G k), (G.expand k).IsMinCut s t Z →
      (G.expand k).cutValue Z ≤ (k : ℕ∞) →
      ∀ p ∈ Z, G.inf p.1.1 = false ∧ p = G.unitArc k p.1.1 := by sorry

end ConstrainedDirSep.STSep
