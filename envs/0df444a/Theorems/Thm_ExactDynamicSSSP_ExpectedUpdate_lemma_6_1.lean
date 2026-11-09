-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_6_1
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:38:52.112182+00:00
-- url     : https://prove2.me/theorems/a5bd6c0f-8fed-4c70-8e0e-3ba07930dbd8
-- title:
--   Lemma 6.1 — random updates preserve the uniform fixed-edge-count law
-- statement:
--   Fix $n\ge3$, $C>0$, a source $s$, an initial edge count $m_0\le N$ and an operation-type sequence. Run the random update process (initial graph from $\mathcal G_{n,m_0}$ with independent $U[0,C)$ weights). Then:
--
--   1. **Invariance.** After $t$ valid updates the weighted graph has law $\mathcal G_{n,m_t}$ with independent $U[0,C)$ weights, $m_t$ the resulting edge count.
--   2. **Insertion.** If step $t$ is an insertion at edge count $m$, then for every measurable set $B$ of weighted graphs and every arc $a$,
--   $$\Pr\bigl(G_{t+1}\in B,\ a_t=a\bigr)=\frac1{m+1}\,\Pr_{m+1}\bigl(G\in B,\ a\in E(G)\bigr),$$
--   i.e. conditional on the final weighted graph the inserted arc is uniform among its $m+1$ arcs.
--   3. **Resampling.** If step $t$ is a resampling at edge count $m$, then for every arc set $S_0$, arc $a$ and measurable set $W$ of weight vectors,
--   $$\Pr(E_t=S_0,\ a_t=a,\ w_t\in W)=\tfrac1m\mathbf 1[a\in S_0]\,\Pr(E_t=S_0,\ w_t\in W),$$
--   and the same identity holds with the new weight vector $w_{t+1}$ in place of $w_t$: conditional on the structure the selected arc is uniform and independent of each of the old and new weight vectors separately.
--
--   Differences from the source:
--   - encoding: conditional on the arc set, the present arcs carry independent U[0,C) weights → a U[0,C) weight is drawn independently for each of the n² ordered pairs (including unused diagonal coordinates), and the graph uses the weights of its present arcs (truncated at 0, a null event); reason: the weighted graph has exactly the source's law
--   - encoding: the updated arc is chosen uniformly among the existing (resp. missing) arcs → the arc of index ⌊U·k⌋ in a fixed enumeration of the k candidates, with U ~ U[0,1) independent of everything else; reason: this realizes exactly the uniform choice; the selection fails only on the null event U ∉ [0,1)
--   - generalization: the product weight law of the present arcs is preserved → the whole n²-vector of weights (present, absent and diagonal pairs) is i.i.d. U[0,C) and independent of the arc set at every step; reason: marginalizing to the present arcs gives the source's statement
--   - encoding: 'conditional on the structure, the selected arc is uniform and independent of each of the old and new weight vectors separately' → the factorization of the joint probabilities of (arc set, selected arc, old weights) and of (arc set, selected arc, new weights); reason: these factorizations are the conditional uniformity and the two separate independences
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 6.1, PDF p.8 = printed p.8

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 6.1 (PDF p. 8). (a) Every random update preserves the law: after `t` valid updates the
weighted graph has law `𝒢_{n,m_t}` with independent `U[0,C)` weights, `m_t` the resulting edge
count. (b) Conditional on the final weighted graph after an insertion, the inserted arc is
uniform among its `m + 1` arcs. (c) For a resampling, conditional on the arc set, the selected
arc is uniform and independent of the old weight vector, and (separately) of the new one. -/
theorem lemma_6_1 {n : ℕ} (hn : 3 ≤ n) (C : ℝ) (hC : 0 < C) (s : Fin n) (m₀ : ℕ)
    (ops : ℕ → UpdKind) (H : ℕ) :
    (∀ t ≤ H, ValidOps n m₀ ops t →
      (procMeasure n C m₀ H).map (fun ω => (procState s ops H ω t).1) =
        gnm n C (edgeCount m₀ ops t)) ∧
    (∀ t < H, ValidOps n m₀ ops (t + 1) → ops t = .insert →
      ∀ B : Set (Sample n), MeasurableSet B → ∀ a : Fin n × Fin n,
        procMeasure n C m₀ H
            {ω | (procState s ops H ω (t + 1)).1 ∈ B ∧ procArc s ops H ω t = some a} =
          ((edgeCount m₀ ops t + 1 : ℕ) : ℝ≥0∞)⁻¹ *
            gnm n C (edgeCount m₀ ops t + 1) (B ∩ {g | a ∈ g.1})) ∧
    (∀ t < H, ValidOps n m₀ ops (t + 1) → ops t = .resample →
      ∀ (S₀ : Finset (Fin n × Fin n)) (a : Fin n × Fin n) (W : Set (Fin n × Fin n → ℝ)),
        MeasurableSet W →
        procMeasure n C m₀ H
            {ω | (procState s ops H ω t).1.1 = S₀ ∧ procArc s ops H ω t = some a ∧
              (procState s ops H ω t).1.2 ∈ W} =
          (edgeCount m₀ ops t : ℝ≥0∞)⁻¹ * (if a ∈ S₀ then 1 else 0) *
            procMeasure n C m₀ H
              {ω | (procState s ops H ω t).1.1 = S₀ ∧ (procState s ops H ω t).1.2 ∈ W} ∧
        procMeasure n C m₀ H
            {ω | (procState s ops H ω t).1.1 = S₀ ∧ procArc s ops H ω t = some a ∧
              (procState s ops H ω (t + 1)).1.2 ∈ W} =
          (edgeCount m₀ ops t : ℝ≥0∞)⁻¹ * (if a ∈ S₀ then 1 else 0) *
            procMeasure n C m₀ H
              {ω | (procState s ops H ω t).1.1 = S₀ ∧ (procState s ops H ω (t + 1)).1.2 ∈ W})
    := by sorry

end ExactDynamicSSSP.ExpectedUpdate
