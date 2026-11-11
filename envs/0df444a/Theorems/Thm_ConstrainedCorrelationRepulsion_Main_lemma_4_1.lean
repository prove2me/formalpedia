-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_4_1
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:43.334955+00:00
-- url     : https://prove2.me/theorems/aafbbe75-e4f8-4752-b420-2dbc21225c9f
-- title:
--   Lemma 4.1 — atoms, outsider counts and separation in every optimum
-- statement:
--   Let $I$ be unweighted with only cannot-links, and let $Q$ have at least two vertices, no internal hard pair, $\delta_Q<|Q|/20$, and a two-witness expansion from its dangerous outsiders. Then every optimum keeps $Q$ together. For its cluster $C$ in any optimum,
--
--   $$
--   |C\setminus Q|\le2\delta_Q.
--   $$
--
--   Any two disjoint sets satisfying these same hypotheses lie in different clusters in every optimum. The dangerous-outsider threshold is $|Q|/3$ and witnesses cannot be reused.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - generalization: the normalized unweighted instance entering Section 4 → any unweighted instance with only cannot-links; reason: the preservation and outsider-count proof uses no normalization or positive-degree assumption
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 4.1, printed p.18 (PDF p.19), proof continuing printed p.19 (PDF p.20)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Units

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_4_1 {n : ℕ} (I : Instance n) (hI : FeasibleInput I)
    (hM : I.mustLink = ⊥) (Q : Finset (Fin n)) (hQ : AtomHypotheses I Q) :
  IsAtom I Q ∧
  (∀ P, Optimal I P → ∀ u ∈ Q,
    ((Finset.univ.filter (fun v => P v = P u ∧ v ∉ Q)).card : ℝ) ≤ 2 * (deltaQ I Q : ℝ)) ∧
  (∀ B : Finset (Fin n), AtomHypotheses I B → Disjoint Q B →
    ∀ P, Optimal I P → ∀ u ∈ Q, ∀ v ∈ B, P u ≠ P v) := by sorry

end ConstrainedCorrelationRepulsion.Main
