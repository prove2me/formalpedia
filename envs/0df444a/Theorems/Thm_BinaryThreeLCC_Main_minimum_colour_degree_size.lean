-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_minimum_colour_degree_size
-- name    : BinaryThreeLCC.Main.minimum_colour_degree_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:02:03.536085+00:00
-- url     : https://prove2.me/theorems/655bf518-6d96-40c7-a2dd-36a5c21b6127
-- title:
--   Fact 3.2 — minimum colour degree (corrected: nonempty vertices)
-- statement:
--   Let $G$ be a finite edge-coloured multigraph with a nonempty vertex set $V$. The colour degree $c(v)$ counts colours with positive incident degree at $v$. Suppose $G$ has no unique-colour cycle and $c(v)\ge k'$ for every vertex. Then
--
--   $$|V|\ge2^{k'},\qquad k'\le\log_2|V|.$$
--
--   Both equivalent conclusions are included. Colours may be unused, edges may be parallel, and $k'$ may be any real threshold.
--
--   Differences from the source:
--   - correction: V may be empty → V is nonempty; reason: the empty vertex set with one empty colour class and k′=0 meets the printed hypotheses but 0 < 2⁰
--   - reading: Section 3 allows loops but Definition 3.1 writes two-element edges → labelled endpoint pairs, loops of length one, parallel-edge cycles of length two, and loops counted twice in undirected degrees and adjacency; reason: the standing multigraph convention and A_T = Q_T + Q_T transpose control the interpretation
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
--   - generalization: the proof inducts on the integer colour-degree threshold → the threshold k′ is any real number; reason: integer colour degrees at least k′ are at least its ceiling; negative thresholds follow from |V| ≥ 1
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Fact 3.2, printed p. 9, PDF p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Graphs

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Fact 3.2, with its necessary nonempty-vertex correction. -/
theorem minimum_colour_degree_size {V E I : Type} [Fintype V] [Fintype E] [Fintype I]
    [Nonempty V] (G : ColouredGraph V E I) (k' : ℝ)
    (hdegree : ∀ v, k' ≤ (numberOfColours G v : ℝ)) (hcycle : NoUniqueColourCycle G) :
    (2 : ℝ) ^ k' ≤ (Fintype.card V : ℝ) ∧
      k' ≤ Real.logb 2 (Fintype.card V) := by sorry

end BinaryThreeLCC.Main
