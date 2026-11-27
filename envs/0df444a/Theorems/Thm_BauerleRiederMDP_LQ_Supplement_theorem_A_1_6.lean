-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_A_1_6
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_A_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:10:20.258408+00:00
-- url     : https://prove2.me/theorems/98317821-d7d9-4680-913a-4da27de30f33
-- title:
--   Theorem A.1.6 — weakly increasing sequence: the limit exists and lim sup = sup lim
-- statement:
--   Let $(v_n)$ be a sequence of functions $v_n : M \to  \mathbb R $ and $(\delta _n) \subset  \mathbb R _+$ with $\lim  \delta _n = 0$ such that $v_n(a) \ge  v_m(a) - \delta _m$ for $a \in  M$, $n \ge  m$. Then the limit $v_\infty  := \lim  v_n$ exists and $\lim _n \sup _{a \in  M} v_n(a) = \sup _{a \in  M} \lim _n v_n(a) = \sup _{a \in  M} v_\infty (a)$.
--
--   **Formalization Note.** No topology, measurability or compactness of $M$ is assumed (none is used). The limit may be $+\infty $ and the suprema may be $+\infty $, so they are taken in `EReal`; for empty $M$ both suprema are $-\infty $. The middle term $\sup _a \lim _n v_n(a)$ is $\sup _a v_\infty (a)$ by the definition of $v_\infty $.
--
--   Differences from the source:
--   - generalization: M a metric space → M an arbitrary type; reason: no topology is used; metric spaces are a special case
--   - encoding: real limits → limits and suprema in [−∞,∞]; reason: the limit can be +∞
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem A.1.6, p.350 (PDF 356)

import Mathlib

open Filter Topology

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem A.1.6** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem A.1.6, p.350, PDF 356). Let `(v_n)` be a sequence of functions `v_n : M → ℝ` and
`(δ_n) ⊂ ℝ_+` with `lim δ_n = 0` such that `v_n(a) ≥ v_m(a) − δ_m` for `a ∈ M`, `n ≥ m`. Then the
limit `v_∞ := lim v_n` exists and
`lim_n sup_{a ∈ M} v_n(a) = sup_{a ∈ M} lim_n v_n(a) = sup_{a ∈ M} v_∞(a)`.

**Formalization Note.** No topology, measurability or compactness of `M` is assumed (none is used).
The limit may be `+∞` and the suprema may be `+∞`, so they are taken in `EReal`; for empty `M` both
suprema are `−∞`. The middle term `sup_a lim_n v_n(a)` is `sup_a v_∞(a)` by the definition of
`v_∞`. -/
theorem theorem_A_1_6 {M : Type*} (v : ℕ → M → ℝ)
    (δ : ℕ → ℝ) (hδ_nonneg : ∀ n, 0 ≤ δ n) (hδ_lim : Tendsto δ atTop (𝓝 0))
    (hinc : ∀ a n m, m ≤ n → v m a - δ m ≤ v n a) :
    ∃ vinf : M → EReal,
      (∀ a, Tendsto (fun n => (v n a : EReal)) atTop (𝓝 (vinf a))) ∧
      Tendsto (fun n => ⨆ a, (v n a : EReal)) atTop (𝓝 (⨆ a, vinf a)) := by sorry

end BauerleRiederMDP.LQ.Supplement
