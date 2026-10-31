-- Prove2me | Theorems.Thm_ApproxVI_lemma_7
-- name    : ApproxVI.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:28.741034+00:00
-- url     : https://prove2.me/theorems/2166c5a1-2df1-431a-aaae-b4fbc8e75d55
-- title:
--   Lemma 7 — block sums of $a(i)M_{i+1}$ exceed $c$ only finitely often
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $(\mathcal F_n)$. Let the step sizes satisfy (AV4): $a(n)\ge0$, $\sum_na(n)=\infty$, $\sum_na(n)^2<\infty$, and $t_n=\sum_{m<n}a(m)$. Let $(M_{n+1})$ be a square-integrable martingale difference sequence ($M_{n+1}$ is $\mathcal F_{n+1}$-measurable and $E[M_{n+1}\mid\mathcal F_n]=0$) such that
--
--   $$
--   E\big[\|M_{n+1}\|^2\mid\mathcal F_n\big]\le K\big(1+\|x_n\|^2\big),\qquad K>0,
--   $$
--
--   for iterates $(x_n)$ with $\sup_n\|x_n\|\le C_1$ almost surely. Let the block indices $m(n),l(n)$ satisfy $t_{l(n)}>t_{m(n)}$, $t_{m(n+1)}>t_{l(n)}$ and $t_{l(n)}-t_{m(n)}\to0$. Fix $c>0$ and set
--
--   $$
--   \psi_n=\Big\|\sum_{i=m(n)}^{l(n)-1}a(i)M_{i+1}\Big\|.
--   $$
--
--   Then $P(\{\psi_n>c\}\ \text{i.o.})=0$.
--
--   This lemma is what allows the stability analysis to use the state-dependent noise bound (AV5) in place of bounded noise.
--
--   **Formalization Note** $\|\cdot\|$ is the Euclidean norm. "i.o. with probability $0$" is written as: almost surely, $\psi_n\le c$ for all large $n$.
--
--   Differences from the source:
--   - generalization: index sequences m(n), l(n) → indices m(n)(ω), l(n)(ω) that may depend on the sample point, with the hypotheses for every ω; reason: deterministic indices are the constant case; the source applies the lemma to random jump times (p.28)
--   - generalization: x_n the iterates of the projective scheme (18), with (AV5) at x_n and sup_n ‖x_n‖ ≤ C₁ a.s. → any process x_n with the conditional variance bound and sup_n ‖x_n‖ ≤ C₁ a.s.; reason: the proof uses only these two properties of x_n; the projective iterates are an instance
--   - encoding: P({ψ_n > c} i.o.) = 0 → ∀ᵐ ω, eventually ψ_n(ω) ≤ c; reason: the same event
--   - encoding: E M²_{n+1} < ∞ → MemLp (M (n+1)) 2 μ; reason: square integrability in Mathlib's form; same instances
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, Lemma 7, p.27

import Mathlib
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ApproxVI_tSeq

namespace ApproxVI

open MeasureTheory Filter Topology

/-- **Lemma 7**, Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration Algorithms*,
arXiv:1709.04673v5, p.27: let `{t_{m(n)}, t_{l(n)}}` be such that `t_{l(n)} > t_{m(n)}`,
`t_{m(n+1)} > t_{l(n)}` and `lim (t_{l(n)} − t_{m(n)}) = 0`. Fix `c > 0` and let
`ψₙ := ‖Σ_{i=m(n)}^{l(n)−1} a(i) M_{i+1}‖`. Then `P({ψₙ > c} i.o.) = 0` within the context of
the projective scheme (18).

"Within the context of the projective scheme" (proof, p.27): the step sizes satisfy (AV4);
`(Mₙ, ℱₙ)` is a square-integrable martingale difference sequence with
`E[‖Mₙ₊₁‖² | ℱₙ] ≤ K(1 + ‖xₙ‖²)` ((AV5) at the projective iterates `xₙ`); and almost surely
`sup ‖xₙ‖ ≤ C₁ < ∞`.

**Formalization Note** `‖·‖` is the Euclidean norm; `tₙ = Σ_{m<n} a(m)` (`tSeq`). The block
indices `m(n), l(n)` may depend on the sample point (the proof of Lemma 4 on p.28 applies the
lemma to such indices); their hypotheses are required for every sample point.
`P({ψₙ > c} i.o.) = 0` is written `∀ᵐ ω, ∀ᶠ n, ψₙ(ω) ≤ c`. The iterates `xₙ` enter only
through the conditional variance bound and the almost-sure bound `C₁`. -/
theorem lemma_7 {d : ℕ} {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (a : ℕ → ℝ) (ha_nonneg : ∀ n, 0 ≤ a n)
    (ha_div : Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop atTop)
    (ha_sq : Summable fun n => a n ^ 2)
    (M x : ℕ → Ω → Fin d → ℝ)
    (hM_adapt : ∀ n, StronglyMeasurable[ℱ (n + 1)] (M (n + 1)))
    (hM_sq : ∀ n, MemLp (M (n + 1)) 2 μ)
    (hM_mds : ∀ n, μ[M (n + 1) | ℱ n] =ᵐ[μ] 0)
    (K : ℝ) (hK : 0 < K)
    (hM_var : ∀ n, μ[fun ω => euclNorm (M (n + 1) ω) ^ 2 | ℱ n]
      ≤ᵐ[μ] fun ω => K * (1 + euclNorm (x n ω) ^ 2))
    (C₁ : ℝ) (hx_bdd : ∀ᵐ ω ∂μ, ∀ n, euclNorm (x n ω) ≤ C₁)
    (m l : ℕ → Ω → ℕ)
    (hml : ∀ ω n, tSeq a (m n ω) < tSeq a (l n ω))
    (hlm : ∀ ω n, tSeq a (l n ω) < tSeq a (m (n + 1) ω))
    (hlim : ∀ ω, Tendsto (fun n => tSeq a (l n ω) - tSeq a (m n ω)) atTop (𝓝 0))
    (c : ℝ) (hc : 0 < c) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      euclNorm (∑ i ∈ Finset.Ico (m n ω) (l n ω), a i • M (i + 1) ω) ≤ c := by sorry

end ApproxVI
