-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_3_4
-- name    : BinaryQueryLB.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:48:53.41757+00:00
-- url     : https://prove2.me/theorems/cd69c949-9213-4764-ac09-853098ce245d
-- title:
--   Lemma 3.4 (Output forcing) — $\prod_i\mu^*(P_i)\le(\omega_m\tau^m)^m\theta^{m^2/2}$
-- statement:
--   Let $d\ge2$, $R,M>0$, $m=\lfloor d/2\rfloor$, and let $\varepsilon>0$ satisfy $C_K\sqrt m\,\varepsilon<MR$, where $C_K=128(\Gamma+1)^2$. Put
--   $$
--   \theta=\Big(\frac{C_K\sqrt m\,\varepsilon}{MR}\Big)^{1/2}<1 .
--   $$
--   Let $P_1,\dots,P_m\subseteq\tau\mathbb B_m$ be sets with positive outer measure. If some $\hat y\in X$ is $\varepsilon$-optimal for $F_W$ for every $W\in P_1\times\dots\times P_m$, then
--   $$
--   \prod_{i=1}^m\mu^*(P_i)\le(\omega_m\tau^m)^m\,\theta^{m^2/2}.
--   $$
--
--   A common $\varepsilon$-optimal output thus forces the volume potential down by a factor that is a power of $\varepsilon$ with exponent of order $m^2$.
--
--   Differences from the source:
--   - encoding: m = ⌊d/2⌋ → m = d / 2 (natural-number division); reason: the same number
--   - encoding: Lebesgue outer measure µ* → MeasureTheory.volume evaluated on arbitrary sets, values in ℝ≥0∞; reason: volume on an arbitrary set is its outer measure
--   - encoding: f(ŷ) − min_X f ≤ ε with ŷ ∈ X → ŷ ∈ X and f(ŷ) ≤ f(y) + ε for all y ∈ X; reason: the minimum over X is attained for the functions considered, so the two forms agree
--   - encoding: put θ = (…)^{1/2} < 1 → θ < 1 is a conclusion; θ^{m²/2} is a real power; reason: θ < 1 follows from the hypothesis
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 3.4, p.17

import Mathlib
import Definitions.Def_BinaryQueryLB_FW__386b32
import Definitions.Def_BinaryQueryLB_IsEpsOptimal
import Definitions.Def_BinaryQueryLB_omegaVol
import Definitions.Def_BinaryQueryLB_tau
import Definitions.Def_BinaryQueryLB_CK

namespace BinaryQueryLB

/-- **Lemma 3.4 (Output forcing).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 3.4, p.17: "Let `ε > 0` satisfy `C_K√m ε < MR`, and put
`θ = (C_K√m ε/(MR))^{1/2} < 1`. Let `P_1, …, P_m ⊆ τB_m` be sets with positive outer measure. If some
`ŷ ∈ X` is ε-optimal for `F_W` for every `W ∈ P_1 × ⋯ × P_m`, then
`∏_{i=1}^m µ*(P_i) ≤ (ω_m τ^m)^m θ^{m²/2}`."

**Formalization Note.** `d ≥ 2`, `R, M > 0`, `m = d / 2`. The sets `P_i` are arbitrary (not assumed
measurable or convex); `µ*` is `volume` on arbitrary sets and the product is in `ℝ≥0∞`. The
conclusion also records `θ < 1`. `θ^{m²/2}` is a real power. -/
theorem lemma_3_4 (d : ℕ) (hd : 2 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε)
    (hεK : CK * Real.sqrt ((d / 2 : ℕ) : ℝ) * ε < M * R)
    (P : Fin (d / 2) → Set (EuclideanSpace ℝ (Fin (d / 2))))
    (hP : ∀ i, P i ⊆ Metric.closedBall 0 (tau (d / 2))) (hPpos : ∀ i, 0 < MeasureTheory.volume (P i))
    (yh : EuclideanSpace ℝ (Fin d))
    (hyh : ∀ W : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2)), (∀ i, W i ∈ P i) → IsEpsOptimal d R (FW d R M W) ε yh) :
    Real.sqrt (CK * Real.sqrt ((d / 2 : ℕ) : ℝ) * ε / (M * R)) < 1 ∧
      ∏ i, MeasureTheory.volume (P i) ≤
        ENNReal.ofReal ((omegaVol (d / 2) * tau (d / 2) ^ (d / 2)) ^ (d / 2) *
          Real.sqrt (CK * Real.sqrt ((d / 2 : ℕ) : ℝ) * ε / (M * R)) ^ (((d / 2 : ℕ) : ℝ) ^ 2 / 2)) := by sorry

end BinaryQueryLB
