-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_local_variance_palette_bound
-- name    : BinaryThreeLCC.Main.local_variance_palette_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:02:00.218552+00:00
-- url     : https://prove2.me/theorems/34593e62-6068-4b66-aa8f-bcb0b8d94af0
-- title:
--   Lemma 5.3 — local variance bounds the palette (corrected: nonempty edges)
-- statement:
--   Let $G=(V,E_1,\ldots,E_k)$ be a finite edge-coloured multigraph with a nonempty vertex set, a nonempty palette, and $|E|>0$ edge copies in total. Degrees count multiplicity, and loops twice. Write $d_i(v)$ for the degree at colour $i$ and $d(v)$ for total degree. Suppose $G$ has no cycle using any colour exactly once. If independent uniform averages satisfy
--
--   $$\mathcal V=\mathbb E_{v\in V}\mathbb E_{i\in[k]}
--   \left(d_i(v)-\frac{d(v)}k\right)^2
--   \le\left(\frac{|E|}{k|V|}\right)^2,$$
--
--   then
--
--   $$k\le60\log_2|V|.$$
--
--   Unused palette colours are allowed. Unique-colour cycles are not replaced with rainbow cycles, and two distinct parallel copies can form a length-two cycle.
--
--   Differences from the source:
--   - correction: the printed hypotheses allow |E|=0 → |E| > 0; reason: two vertices, 61 empty colour classes and no edges give variance zero, but 61 > 60 log₂2
--   - reading: Section 3 allows loops but Definition 3.1 writes two-element edges → labelled endpoint pairs, loops of length one, parallel-edge cycles of length two, and loops counted twice in undirected degrees and adjacency; reason: the standing multigraph convention and A_T = Q_T + Q_T transpose control the interpretation
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
--   - encoding: uniform expectations over vertices and colours → nonempty averaging sets and the exact finite sum divided by its cardinality; reason: these are the defined domains of both displayed expectations
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Lemma 5.3, printed p. 14, PDF p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Graphs

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Lemma 5.3, with its necessary nonempty-edge correction. -/
theorem local_variance_palette_bound {V E I : Type} [Fintype V] [Fintype E] [Fintype I]
    (G : ColouredGraph V E I)
    (hcycle : NoUniqueColourCycle G) (hedges : 0 < Fintype.card E)
    (hvar : localVariance G ≤
      ((Fintype.card E : ℝ) / ((Fintype.card I : ℝ) * Fintype.card V)) ^ 2) :
    (Fintype.card I : ℝ) ≤ 60 * Real.logb 2 (Fintype.card V) := by sorry

end BinaryThreeLCC.Main
