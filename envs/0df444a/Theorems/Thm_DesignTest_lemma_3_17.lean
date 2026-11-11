-- Prove2me | Theorems.Thm_DesignTest_lemma_3_17
-- name    : DesignTest.lemma_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:07.412839+00:00
-- url     : https://prove2.me/theorems/29c9671b-c45c-463d-a526-379724de6ee3
-- title:
--   Lemma 3.17 (rank–collision) — $\mathrm{Dist}_1(\Phi(\mu),\Phi(\nu_{C,\lambda}))\ge\lambda/2>\varepsilon_{\mathrm{far}}$ and $m\ge\sqrt{2(1-2\delta_{\mathrm{fail}})M}/(2\varepsilon_{\mathrm{far}})$
-- statement:
--   Let $\mathcal X$ be a measurable space, $\Phi$ a measurable map from $\mathcal X$ to the rank-one projectors on $\mathbb C^n$, and $\mu$ a probability measure on $\mathcal X$. Put $K=\|\Phi(\mu)\|_\infty^{-1}$ and $M=\lfloor K/2\rfloor$, and assume $K\ge2$. Let $\varepsilon_{\mathrm{far}}\in(0,1/2)$ and $\delta_{\mathrm{fail}}\in[0,1/2)$. For a list $C=(X_1,\dots,X_M)$ and $\lambda\in(2\varepsilon_{\mathrm{far}},1]$ let $\nu_{C,\lambda}=(1-\lambda)\mu+\lambda\widehat\mu_C$, $\widehat\mu_C=M^{-1}\sum_a\delta_{X_a}$.
--   1. For every list $C$,
--   $$\mathrm{Dist}_1(\Phi(\mu),\Phi(\nu_{C,\lambda}))\ge\lambda\Big(1-\frac MK\Big)\ge\frac\lambda2>\varepsilon_{\mathrm{far}} .$$
--   2. If an integer $m\ge0$ and a measurable $f:\mathcal X^m\to[0,1]$ satisfy $\mathbb E_{\mu^{\otimes m}}[f]\ge1-\delta_{\mathrm{fail}}$ and $\mathbb E_{C\sim\mu^{\otimes M}}\big[\mathbb E_{\nu_{C,\lambda}^{\otimes m}}[f]\big]\le\delta_{\mathrm{fail}}$ for every $\lambda\in(2\varepsilon_{\mathrm{far}},1]$, then
--   $$m\ge\frac{\sqrt{2(1-2\delta_{\mathrm{fail}})M}}{2\varepsilon_{\mathrm{far}}} .$$
--
--   The list $C$ is drawn once and held fixed while the $m$ samples are drawn from $\nu_{C,\lambda}$. The lemma yields both the state and the unitary sample lower bounds of the paper.
--
--   **Formalization Note** $\Phi(\nu)$ is the entrywise integral; $\|\cdot\|_\infty$ is the published `DistQuantumQuery.opNorm` (Mathlib's $\ell^2$ operator norm, the largest singular value); $\mathrm{Dist}_1(A,B)=\frac12\|A-B\|_1$ with the published trace norm. Measurability of $\Phi$ is entrywise; the hidden-list average is the iterated integral over $\mu^{\otimes M}$.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and a measurable map Φ into its rank-one projectors → H = ℂ^n and Φ : X → Matrix (Fin n) (Fin n) ℂ with every Φ x = |v⟩⟨v| for a unit vector v, measurable entrywise; reason: every finite-dimensional Hilbert space is ℂ^n up to a unitary, which preserves all quantities of the lemma
--   - encoding: trace norm ‖A‖₁ = Tr|A| → DistQuantumQuery.traceNorm A = Σ_i √λ_i(A†A), the sum of the singular values; reason: the same quantity, written without a square root of an operator
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Lemma 3.17, p.21

import Mathlib
import Definitions.Def_DistQuantumQuery_traceNorm
import Definitions.Def_DesignTest_rankOneMoment

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Lemma 3.17** (Rank–collision lemma). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary
Designs*, STOC 2027 submission (sha256 e2f0a429…), Lemma 3.17, p.21.

Let `X` be a measurable space, `Φ` a measurable map from `X` to the rank-one projectors on `ℂ^n`, and
`µ` a probability measure on `X`. Put `K := ‖Φ(µ)‖_∞⁻¹`, `M := ⌊K/2⌋`, and assume `K ≥ 2`. Let
`ε_far ∈ (0, 1/2)`, `δ_fail ∈ [0, 1/2)`. For a list `C = (X_1, …, X_M)` and `λ ∈ (2ε_far, 1]` let
`ν_{C,λ} := (1 − λ)µ + λ M⁻¹ Σ_a δ_{X_a}`.
1. For every list `C`, `Dist₁(Φ(µ), Φ(ν_{C,λ})) ≥ λ(1 − M/K) ≥ λ/2 > ε_far`.
2. If an integer `m ≥ 0` and a measurable `f : X^m → [0, 1]` satisfy `E_{µ^{⊗m}}[f] ≥ 1 − δ_fail` and
   `E_{C∼µ^{⊗M}}[E_{ν_{C,λ}^{⊗m}}[f]] ≤ δ_fail` for every `λ ∈ (2ε_far, 1]`, then
   `m ≥ √(2(1 − 2δ_fail)M)/(2ε_far)`.

**Formalization Note.** `Φ(ν)` is the entrywise integral (`rankOneMoment`); `‖·‖_∞` is the published
`DistQuantumQuery.opNorm` (Mathlib's L2 operator norm, the largest singular value) and
`Dist₁(A, B) = ½‖A − B‖₁` with the published `DistQuantumQuery.traceNorm` (sum of singular values). Measurability of `Φ` is entrywise. The list `C`
is drawn once from `µ^{⊗M}` and held fixed while the `m` samples are drawn from `ν_{C,λ}`. -/
theorem lemma_3_17 {X : Type} [MeasurableSpace X] (n : ℕ) (Φ : X → Matrix (Fin n) (Fin n) ℂ)
    (hΦmeas : ∀ i j, Measurable fun x => Φ x i j) (hΦ : ∀ x, IsRankOneProj (Φ x))
    (μ : Measure X) [IsProbabilityMeasure μ] (εfar δ : ℝ) (hε0 : 0 < εfar) (hε1 : εfar < 1 / 2)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    let K := (DistQuantumQuery.opNorm (rankOneMoment Φ μ))⁻¹
    let M := ⌊K / 2⌋₊
    2 ≤ K →
      (∀ (c : Fin M → X) (lam : ℝ), 2 * εfar < lam → lam ≤ 1 →
          lam * (1 - (M : ℝ) / K) ≤
              DistQuantumQuery.traceNorm
                (rankOneMoment Φ μ - rankOneMoment Φ (empiricalMixture μ lam c)) / 2 ∧
            lam / 2 ≤ lam * (1 - (M : ℝ) / K) ∧ εfar < lam / 2) ∧
        ∀ (m : ℕ) (f : (Fin m → X) → ℝ), Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
          1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => μ) →
          (∀ lam : ℝ, 2 * εfar < lam → lam ≤ 1 →
              ∫ c, (∫ x, f x ∂(Measure.pi fun _ : Fin m => empiricalMixture μ lam c))
                  ∂(Measure.pi fun _ : Fin M => μ) ≤ δ) →
          Real.sqrt (2 * (1 - 2 * δ) * (M : ℝ)) / (2 * εfar) ≤ (m : ℝ) := by sorry

end DesignTest
