-- Prove2me | Theorems.Thm_AuditAdapt_Supplement_theorem_5_3
-- name    : AuditAdapt.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:37:59.603185+00:00
-- url     : https://prove2.me/theorems/561d3b36-2a4a-47c8-af75-fe71b44fa933
-- title:
--   Theorem 5.3, p.5 — upper bound: median-of-means IPW is $(\delta,\eta)$-accurate once $T\ge\lceil4\bar\chi^2(\pi)/\delta^2\rceil\lceil8\ln(1/\eta)\rceil$
-- statement:
--   Consider the contextual-bandit auditing problem of §5.1: contexts $x_t\sim\mathcal D$ are i.i.d. on a measurable space $\mathcal X$; given $x_t$, a cost vector $\ell_t\in[0,1]^{\mathcal A}$ is drawn with mean $c(x_t)$ and the action $a_t\sim\pi(\cdot\mid x_t)$ is drawn independently of $\ell_t$. The auditor observes $\{(x_t,\pi(\cdot\mid x_t),a_t,\ell_t(a_t))\}_{t=1}^T$ and knows $\bar p=\mathbb E_x\pi(\cdot\mid x)$; the target is $\Delta(\pi)=\mathbb E_x\langle c(x),\pi(\cdot\mid x)\rangle-\langle\mathbb E_xc(x),\bar p\rangle$. An auditor is **$(\delta,\eta)$-accurate** on an instance if its output $\widehat\Delta$ satisfies $\mathbb P(|\widehat\Delta-\Delta(\pi)|<\delta)\ge1-\eta$.
--
--   Let $w_t=\bar p(a_t)/\pi(a_t\mid x_t)$ and $Y_t=\ell_t(a_t)(1-w_t)$. Split the $T$ rounds into
--
--   $$
--   k=\lceil 8\ln(1/\eta)\rceil\ \text{ blocks of }\ m=\Big\lceil\frac{4\bar\chi^2(\pi)}{\delta^2}\Big\rceil\ \text{ rounds each},
--   $$
--
--   and output the median of the block means of the $Y_t$. If $\bar\chi^2(\pi)<\infty$, this auditor is $(\delta,\eta)$-accurate on every instance once
--
--   $$
--   T\ \ge\ \Big\lceil\frac{4\bar\chi^2(\pi)}{\delta^2}\Big\rceil\cdot\big\lceil 8\ln(1/\eta)\big\rceil .
--   $$
--
--   A policy can be audited from its own logs at a rate governed by $\bar\chi^2(\pi)=\mathbb E_x[\chi^2(\bar p\,\|\,\pi(\cdot\mid x))]$, i.e. by how much it explores the actions its marginal uses; Theorem 5.4 shows this is optimal up to constants.
--
--   **Formalization Note** The conclusion is stated for every median of the $k$ block means; the blocks are the first $mk$ rounds.
--
--   Differences from the source:
--   - encoding: policy π(· | x) ∈ Δ(A), measurable in x → Markov kernel πk : Kernel X A, π(a | x) = (πk x {a}).toReal; reason: a measurable family of distributions on a finite set is a Markov kernel; same instances
--   - encoding: conditional cost law with mean c(x), ℓ ∈ [0, 1]^A → Markov kernel K : Kernel X (A → ℝ) with K(x)-a.s. ℓ ∈ [0, 1]^A for every x, c(x)(a) = ∫ ℓ(a) dK(x); reason: same instances
--   - encoding: x_t ∼ D i.i.d.; ℓ_t and a_t independent given x_t → T-round law Measure.pi of D ⊗ₘ (K ×ₖ πk); reason: the composition-product with the product kernel is conditional independence given x
--   - encoding: χ̄²(π) ∈ [0, ∞] → chiBar D πk, a lower Lebesgue integral in ℝ≥0∞; reason: same value
--   - encoding: (δ, η) with no stated range → hypotheses 0 < δ and 0 < η; reason: δ ≤ 0 makes accuracy impossible and the block length undefined, η ≤ 0 makes ln(1/η) undefined; every η ≥ 1 is allowed (trivial)
--   - encoding: m = ⌈4 χ̄²(π)/δ²⌉ and P(|Δ̂ − Δ(π)| < δ) ≥ 1 − η → ⌈4 (chiBar D πk).toReal / δ²⌉₊ and ENNReal.ofReal (1 − η) ≤ (measure of the event); reason: toReal is exact under the hypothesis χ̄²(π) < ∞; ofReal(1 − η) = 1 − η for η ≤ 1
--   - reading: split T rounds into k blocks of m rounds each (T ≥ mk) → the blocks are the first m·k rounds, consecutive; reason: the source does not say which rounds when T > mk; consecutive blocks from the start are the natural reading and the proof works for any choice
--   - generalization: output the median of the block means → every median selection (any value with at least k/2 block means on each side), measurable or not; reason: specializes to any fixed median rule; for a non-measurable selection the measure of the event is its outer measure
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), Theorem 5.3 (Upper bound), p.5 (PDF p.5), with the setting of §5.1, p.5

import Mathlib
import Definitions.Def_AuditAdapt_Supplement_chiSq
import Definitions.Def_AuditAdapt_Supplement_blockMeans
import Definitions.Def_AuditAdapt_Supplement_banditAdaptivityCost
import Definitions.Def_AuditAdapt_Supplement_banditRoundLaw

namespace AuditAdapt.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Theorem 5.3 (Upper bound), p.5** (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…)). Let `w_t = p̄(a_t)/π(a_t | x_t)` and
`Y_t = ℓ_t(a_t)(1 − w_t)`. Split `T` rounds into `k = ⌈8 ln(1/η)⌉` blocks of `m = ⌈4 χ̄²(π)/δ²⌉` rounds each,
and output the median of the block means. If `χ̄²(π) < ∞`, this auditor is `(δ, η)`-accurate on every
instance once `T ≥ ⌈4 χ̄²(π)/δ²⌉ · ⌈8 ln(1/η)⌉`.

An instance (§5.1, p.5) is a context law `D` on a measurable space `X`, a policy `π(· | x)` (Markov
kernel `πk`) on the finite action set `A`, and a cost law `K(x)` on `[0,1]^A` with mean `c(x)`; rounds
`(x_t, ℓ_t, a_t)` are i.i.d. with law `banditRoundLaw D πk K`. `(δ, η)`-accurate:
`P(|Δ̂ − Δ(π)| < δ) ≥ 1 − η`.

**Formalization Note** The blocks are the first `m·k` rounds (`blockMeans`, samples indexed from `0`).
"The median" is any median: the conclusion holds for every selection `med` with `IsMedian v (med v)`;
for a non-measurable selection the measure of the event is its outer measure. `χ̄²(π)` lies in `ℝ≥0∞`
and enters `m` through `toReal`, which is faithful under `χ̄²(π) < ∞`. `δ > 0` and `η > 0` are implicit
in "(δ, η)"; for `η ≥ 1` the claim is trivial. The costs are only required to lie in `[0,1]^A` almost surely
under each `K(x)`, for every context `x`. -/
theorem theorem_5_3 {X A : Type*} [MeasurableSpace X] [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    (D : Measure X) [IsProbabilityMeasure D] (πk : Kernel X A) [IsMarkovKernel πk]
    (K : Kernel X (A → ℝ)) [IsMarkovKernel K]
    (hK : ∀ x, ∀ᵐ ℓ ∂(K x), ∀ a, ℓ a ∈ Set.Icc (0 : ℝ) 1)
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) (hχ : chiBar D πk < ∞) (T : ℕ)
    (hT : ⌈4 * (chiBar D πk).toReal / δ ^ 2⌉₊ * ⌈8 * Real.log (1 / η)⌉₊ ≤ T)
    (med : (Fin ⌈8 * Real.log (1 / η)⌉₊ → ℝ) → ℝ) (hmed : ∀ v, IsMedian v (med v)) :
    ENNReal.ofReal (1 - η) ≤
      (Measure.pi fun _ : Fin T => banditRoundLaw D πk K)
        {ω | |med (blockMeans ⌈4 * (chiBar D πk).toReal / δ ^ 2⌉₊ ⌈8 * Real.log (1 / η)⌉₊
              (sampleSeq (ipwSample D πk) ω)) - banditAdaptivityCost D πk K| < δ} := by sorry

end AuditAdapt.Supplement
