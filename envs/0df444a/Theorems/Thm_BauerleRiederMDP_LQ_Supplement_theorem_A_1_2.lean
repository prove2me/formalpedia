-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_A_1_2
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_A_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:09:34.692798+00:00
-- url     : https://prove2.me/theorems/7908da1e-0a79-4419-ad51-6990b5b5fe85
-- title:
--   Theorem A.1.2 (corrected: nonempty M) — an upper semicontinuous extended-real function on a nonempty compact metric space attains its supremum
-- statement:
--   Let $M$ be compact. If $v : M \to  \bar{\mathbb R}$ is upper semicontinuous then the function $v$ attains its supremum: there is $b \in  M$ with $v(b) = \sup _{x \in  M} v(x)$.
--
--   **Formalization Note.** Appendix A.1 works on a metric space $M$ (p.347). $\bar{\mathbb R} = [-\infty , \infty ]$ is `EReal`, so both infinite values are allowed and the supremum always exists. $M$ is assumed nonempty: on the empty space nothing is attained (a boundary convention the book leaves implicit).
--
--   Differences from the source:
--   - correction: M compact → M compact and nonempty; reason: false for M = ∅: nothing is attained
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem A.1.2, p.348 (PDF 354)

import Mathlib

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem A.1.2** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem A.1.2, p.348, PDF 354). Let `M` be compact. If `v : M → ℝ̄` is upper
semicontinuous then the function `v` attains its supremum: there is `b ∈ M` with
`v(b) = sup_{x ∈ M} v(x)`.

**Formalization Note.** Appendix A.1 works on a metric space `M` (p.347). `ℝ̄ = [−∞, ∞]` is `EReal`,
so both infinite values are allowed and the supremum always exists. `M` is assumed nonempty: on
the empty space nothing is attained (a boundary convention the book leaves implicit). -/
theorem theorem_A_1_2 {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
    (v : M → EReal) (hv : UpperSemicontinuous v) :
    ∃ b : M, v b = ⨆ x, v x := by sorry

end BauerleRiederMDP.LQ.Supplement
