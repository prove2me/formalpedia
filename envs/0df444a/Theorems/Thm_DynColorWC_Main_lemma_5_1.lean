-- Prove2me | Theorems.Thm_DynColorWC_Main_lemma_5_1
-- name    : DynColorWC.Main.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:47:11.168204+00:00
-- url     : https://prove2.me/theorems/1a9f3f92-87ea-42cf-95ec-90292f08a724
-- title:
--   Lemma 5.1 — the one-shot coloring leaves slack ≥ c·z(v) − O(log n) at every vertex and time, w.h.p.
-- statement:
--   Let $V(\mathrm{II})$ be the set of nodes colored in stage (II) and $z(v)$ the sparsity of $v$ (Definition 3.1). With high probability, simultaneously for all vertices and times,
--   $$\Delta+1-\deg(v)+|N(v)\cap V(\mathrm{II})|-|\chi(N(v)\cap V(\mathrm{II}))|\ge c\,z(v)-O(\log n)$$
--   for a fixed constant $c>0$. The marks and proposals are drawn once and reused at every time of the oblivious sequence.
--
--   Differences from the source:
--
--   - generalization: all times of an oblivious update sequence of length poly(n) (the snapshots G_0, …, G_T) → any list of at most n^d + 1 graphs on Fin n of maximum degree ≤ Δ, fixed before the draw; reason: the proof is a union bound over fixed snapshots; it specializes to G_0, …, G_T with T ≤ n^d
--   - encoding: marks with probability 1/100 and independent uniform q_v ∈ [Δ+1], fixed for the whole run → one draw: each vertex independently draws a uniform pair (r_v, q_v) ∈ {0..99} × Fin (Δ+1), marked iff r_v = 0, used for every snapshot; reason: exactly Bernoulli(1/100) marks and uniform proposals, all independent
--   - encoding: 'with high probability', 'c z(v) − O(log n)', 'a fixed constant c > 0' → ∃ c > 0 absolute, ∀ c′, d > 0 ∃ K: the failure set {∃ snapshot, ∃ v: σ₂(v) < c·z(v) − K log₂ n} has measure ≤ n^{−c′}; reason: w.h.p. as in Theorem 4; c is fixed before c′, d and K after them
--   - encoding: z(v), the sparsity of Definition 3.1 → DynBrooks.sparsity Δ G v = (C(Δ,2) − nbrEdges)/Δ, with Δ ≥ 1 and n ≥ 2; reason: Definition 3.1 normalizes by Δ (undefined at Δ = 0); n ≥ 2 makes log₂ n ≥ 1
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Lemma 5.1, pp. 52–53 (PDF 54–55)

import Mathlib
import Definitions.Def_DynBrooks_Sparsity
import Definitions.Def_DynColorWC_Main_OneShot

namespace DynColorWC.Main

open Classical in
/-- **Lemma 5.1** (One-shot coloring; Flin and Ghaffari (2026), STOC 2027 submission,
sha256 93ebb2ff…3154300e3, pp. 52–53 (PDF 54–55)). Let `V(II)` be the set of nodes colored in
stage (II) and `z(v)` the sparsity of `v` (Definition 3.1). With high probability, simultaneously for
all vertices and times,
`Δ + 1 − deg(v) + |N(v) ∩ V(II)| − |χ(N(v) ∩ V(II))| ≥ c·z(v) − O(log n)`, for a fixed constant
`c > 0`.

Formal reading. There is an absolute `c > 0` such that for all `c′, d > 0` there is `K` with: for
every `n ≥ 2`, every `Δ ≥ 1` and every list of at most `n^d + 1` graphs on `Fin n` of maximum degree
at most `Δ` (the snapshots `G_0, …, G_T` of an oblivious sequence of `T ≤ n^d` updates, fixed before
the draw), the probability, over one draw of marks and proposals used for every snapshot, that some
snapshot and some vertex have slack below `c·z(v) − K log₂ n` is at most `n^{−c′}`. -/
theorem lemma_5_1 :
    ∃ c : ℝ, 0 < c ∧
      ∀ c' d : ℝ, 0 < c' → 0 < d → ∃ K : ℝ,
        ∀ (n Δ : ℕ), 2 ≤ n → 1 ≤ Δ →
          ∀ Gs : List (SimpleGraph (Fin n)), (Gs.length : ℝ) ≤ (n : ℝ) ^ d + 1 →
            (∀ G ∈ Gs, ∀ v, G.degree v ≤ Δ) →
            oneShotMeasure n Δ
              {x | ∃ G ∈ Gs, ∃ v : Fin n,
                stageTwoSlack G x v < c * DynBrooks.sparsity Δ G v - K * Real.logb 2 n}
              ≤ ENNReal.ofReal ((n : ℝ) ^ (-c')) := by sorry

end DynColorWC.Main
