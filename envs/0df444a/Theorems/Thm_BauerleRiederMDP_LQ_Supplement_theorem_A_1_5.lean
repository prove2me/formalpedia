-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_A_1_5
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_A_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:10:00.19109+00:00
-- url     : https://prove2.me/theorems/abf7bc00-74f3-5006-a4d0-86b2ec10c64c
-- title:
--   Theorem A.1.5 (corrected: nonempty M) — compact M, weakly decreasing usc sequence: usc limit, Ls of argmax sets, lim sup = sup lim
-- statement:
--   Let $M$ be compact and let $(v_n)$ be a sequence of upper semicontinuous functions $v_n : M \to  \mathbb R $. Moreover, there exists a sequence $(\delta _n) \subset  \mathbb R _+$ with $\lim  \delta _n = 0$ and $v_n(a) \le  v_m(a) + \delta _m$ for $a \in  M$, $n \ge  m$. Then the limit $v_\infty  := \lim  v_n$ exists and $v_\infty $ is upper semicontinuous. a) Let $A_n := {a \in  M | v_n(a) = \sup _{x \in  M} v_n(x)}$ for $n \in  \mathbb N $ and $n = \infty $. Then $\emptyset  \ne  LsA_n \subset  A_\infty $. b) $\lim _n \sup _{a \in  M} v_n(a) = \sup _{a \in  M} \lim _n v_n(a) = \sup _{a \in  M} v_\infty (a)$.
--
--   **Formalization Note.** $M$ is a nonempty compact metric space (Appendix A.1, p.347; for empty $M$ every $A_n$ is empty and $\emptyset  \ne  LsA_n$ fails, a boundary convention). The $v_n$ are real, but the limit may be $-\infty $ (e.g. $v_n ≡ -n$), so $v_\infty $, the suprema and $A_\infty $ are taken in `EReal`. $A_n$ is written as the set of maximum points $\{a | \forall  x, v_n(x) \le  v_n(a)\}$, which is $\{a | v_n(a) = \sup  v_n\}$. $LsA_n$ is `LsSet`. Part b)'s middle term $\sup _a \lim _n v_n(a)$ is $\sup _a v_\infty (a)$ by the definition of $v_\infty $, so one limit statement covers both equalities.
--
--   Differences from the source:
--   - correction: M compact → M compact and nonempty; reason: for M = ∅ every A_n is empty and ∅ ≠ LsA_n fails
--   - encoding: v_∞ real → v_∞, the suprema and A_∞ in [−∞,∞]; reason: the limit can be −∞ (v_n ≡ −n)
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem A.1.5, p.349-350 (PDF 355)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_LsSet

open Filter Topology

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem A.1.5** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem A.1.5, pp.349–350, PDF 355–356). Let `M` be compact and let `(v_n)` be a sequence of
upper semicontinuous functions `v_n : M → ℝ`. Moreover, there exists a sequence `(δ_n) ⊂ ℝ_+`
with `lim δ_n = 0` and `v_n(a) ≤ v_m(a) + δ_m` for `a ∈ M`, `n ≥ m`. Then the limit
`v_∞ := lim v_n` exists and `v_∞` is upper semicontinuous.
a) Let `A_n := {a ∈ M | v_n(a) = sup_{x ∈ M} v_n(x)}` for `n ∈ ℕ` and `n = ∞`. Then
`∅ ≠ LsA_n ⊂ A_∞`.
b) `lim_n sup_{a ∈ M} v_n(a) = sup_{a ∈ M} lim_n v_n(a) = sup_{a ∈ M} v_∞(a)`.

**Formalization Note.** `M` is a nonempty compact metric space (Appendix A.1, p.347; for empty `M`
every `A_n` is empty and `∅ ≠ LsA_n` fails, a boundary convention). The `v_n` are real, but the
limit may be `−∞` (e.g. `v_n ≡ −n`), so `v_∞`, the suprema and `A_∞` are taken in `EReal`.
`A_n` is written as the set of maximum points `{a | ∀ x, v_n(x) ≤ v_n(a)}`, which is
`{a | v_n(a) = sup v_n}`. `LsA_n` is `LsSet`. Part b)'s middle term `sup_a lim_n v_n(a)` is
`sup_a v_∞(a)` by the definition of `v_∞`, so one limit statement covers both equalities. -/
theorem theorem_A_1_5 {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
    (v : ℕ → M → ℝ) (hv : ∀ n, UpperSemicontinuous (v n))
    (δ : ℕ → ℝ) (hδ_nonneg : ∀ n, 0 ≤ δ n) (hδ_lim : Tendsto δ atTop (𝓝 0))
    (hdec : ∀ a n m, m ≤ n → v n a ≤ v m a + δ m) :
    ∃ vinf : M → EReal,
      (∀ a, Tendsto (fun n => (v n a : EReal)) atTop (𝓝 (vinf a))) ∧
      UpperSemicontinuous vinf ∧
      (LsSet (fun n => {a | ∀ x, v n x ≤ v n a})).Nonempty ∧
      LsSet (fun n => {a | ∀ x, v n x ≤ v n a}) ⊆ {a | ∀ x, vinf x ≤ vinf a} ∧
      Tendsto (fun n => ⨆ a, (v n a : EReal)) atTop (𝓝 (⨆ a, vinf a)) := by sorry

end BauerleRiederMDP.LQ.Supplement
