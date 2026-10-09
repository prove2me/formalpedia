-- Prove2me | Theorems.Thm_ExpanderBIS_Potts_lemma_14
-- name    : ExpanderBIS.Potts.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:29.626902+00:00
-- url     : https://prove2.me/theorems/9c8a0249-e424-442d-8a71-1e24742b0430
-- title:
--   Lemma 14 — count of connected induced subgraphs through a vertex
-- statement:
--   Let $G$ be a finite simple graph of maximum degree at most $\Delta$, with $\Delta\ge1$. For a vertex $v$ and an integer $t\ge0$, the number of connected induced subgraphs of order $t$ containing $v$ is at most
--
--   $$
--   (e\Delta)^t.
--   $$
--
--   The count controls how many size-$t$ polymers can contain one vertex; it is reused in the per-vertex Kotecký–Preiss sum.
--
--   **Formalization Note** The bound $\Delta\ge1$ is explicit because the printed statement fails for an isolated vertex when $\Delta=0$ and $t=1$. Each induced subgraph is identified with its vertex set.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 16, Lemma 14 (citing Galvin and Kahn, Lemma 2.1)

import Mathlib
import Definitions.Def_ExpanderBIS_Potts_Setting

namespace ExpanderBIS.Potts

open Finset

/-- Lemma 14, p. 16, citing Galvin–Kahn Lemma 2.1. -/
theorem lemma_14 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hΔ : 1 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (v : V) (t : ℕ) :
    (#((Finset.univ : Finset (Finset V)).filter
      (fun S => v ∈ S ∧ #S = t ∧ (G.induce (S : Set V)).Connected)) : ℝ) ≤
      (Real.exp 1 * (Δ : ℝ)) ^ t := by sorry

end ExpanderBIS.Potts
