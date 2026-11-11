-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_corollary_6_4
-- name    : CaiFourierSparse.Learning.corollary_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:14:49.844316+00:00
-- url     : https://prove2.me/theorems/13c2fce4-e475-409b-82c7-7f7a8cb91421
-- title:
--   Corollary 6.4 — comparison of filters $M_{\ell,\delta}$ and $M_{k,\varepsilon}$, and filtered almost-orthogonality
-- statement:
--   Let $C\ge64$ be even, $C_M=4C^2$ and $C_H=8C_M$.
--   1. There is a constant $A$ such that for all $\ell\le k$ and $\varepsilon,\delta\in(0,1/2]$ with $\Delta_{\ell,\delta}\le\Delta_{k,\varepsilon}$ and every $\ell$-Fourier-sparse $w$: $\|M_{\ell,\delta}w-M_{k,\varepsilon}w\|_2^2\le A\delta\|M_{k,\varepsilon}w\|_2^2$ (eq. (68)).
--   2. For an $\ell$-Fourier-sparse $w$ and an $r$-Fourier-sparse $z$ with $\ell,r\le k$ whose frequencies are separated by $\min\{C_H\frac{\ell r}\delta(\log\frac{\ell r}\delta+\log\frac k\varepsilon),2\Delta_{k,\varepsilon}\}$: $|\langle M_{k,\varepsilon}w,M_{k,\varepsilon}z\rangle|\le\delta\|M_{k,\varepsilon}w\|_2\|M_{k,\varepsilon}z\|_2$ (eq. (69)).
--
--   Differences from the source:
--   - reading: C ≥ 64 an even integer (§6), C_M a universal constant with Δ_M = (C_M/2)(…) in (67) → every even C ≥ 64, with C_M = 4C² and C_H = 8C_M; reason: Claim 6.5(5) bounds the same radius Δ_M by 2C²(…), so C_M/2 = 2C²; quantifying over every admissible C is the strongest reading
--   - reading: log in the filter constants Δ_{ℓ,δ}, d_min and in the separation thresholds → base-2 logarithm; reason: the Fourier transform of (72) prints ⌈log₂ r⌉; the base of the filter's exponents must be fixed for the objects to be defined
--   - encoding: parameters ℓ, k, ε, δ (any) → 1 ≤ ℓ (and r) ≤ k and ε, δ ∈ (0, 1/2]; reason: the filters M_{ℓ,δ}, M_{k,ε} are built under the section's standing 0 < δ ≤ 1/2; sparsities are positive
--   - encoding: O(δ) → A·δ with A > 0 fixed before ℓ, k, ε, δ, w; reason: universal O-constant (for the fixed filter constant C)
--   - encoding: frequencies separated by a threshold → |f_i − f'_j| ≥ threshold for all i, j; reason: 'separated by' read as at least
--   - encoding: |⟨Mw, Mz⟩| ≤ δ‖Mw‖₂‖Mz‖₂ → the integrand Mw·conj(Mz) is integrable (an added clause) and |⟨Mw, Mz⟩|² ≤ δ²‖Mw‖²₂‖Mz‖²₂; reason: the added integrability makes the inner product the paper's integral rather than a junk 0; squaring is equivalent
--   - encoding: squared L² norms → ℝ≥0∞-valued lower integrals wsq/lsq/osq, real coefficients through ENNReal.ofReal; reason: non-square-integrable functions get energy ∞, so no bound holds through a junk value
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Corollary 6.4, printed p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_Filter

namespace CaiFourierSparse.Learning

open MeasureTheory

/-- Corollary 6.4 (printed p. 32, PDF p. 34). Let `C ≥ 64` be an even integer, `C_M = 4C²`,
`C_H = 8 C_M`, and write `M_{k,ε} = M_{k,k,ε}`, `M_{ℓ,δ} = M_{ℓ,ℓ,δ}`.
(1) For `ℓ ≤ k` and `Δ_{ℓ,δ} ≤ Δ_{k,ε}`, every `ℓ`-Fourier-sparse `w` satisfies
`‖M_{ℓ,δ} w - M_{k,ε} w‖²₂ ≤ O(δ) ‖M_{k,ε} w‖²₂` (eq. (68)).
(2) For an `ℓ`-Fourier-sparse `w` and an `r`-Fourier-sparse `z` with `ℓ, r ≤ k` whose
frequencies are separated by `min{C_H (ℓr/δ)(log(ℓr/δ) + log(k/ε)), 2Δ_{k,ε}}`,
`|⟨M_{k,ε} w, M_{k,ε} z⟩| ≤ δ ‖M_{k,ε} w‖₂ ‖M_{k,ε} z‖₂` (eq. (69), stated squared; the
inner product over `ℝ` is an integral of an integrable function). -/
theorem corollary_6_4 (C : ℕ) (hCe : Even C) (hC : 64 ≤ C) :
    (∃ A : ℝ, 0 < A ∧
      ∀ (ℓ k : ℕ) (ε δ : ℝ), 1 ≤ ℓ → ℓ ≤ k → 0 < ε → ε ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
        filterDelta C ℓ δ ≤ filterDelta C k ε →
        ∀ (α : Fin ℓ → ℂ) (f : Fin ℓ → ℝ),
          lsq (fun t => filtered C ℓ ℓ δ (sparseSignal α f) t -
              filtered C k k ε (sparseSignal α f) t) ≤
            ENNReal.ofReal (A * δ) * lsq (filtered C k k ε (sparseSignal α f))) ∧
    (∀ (ℓ r k : ℕ) (ε δ : ℝ), 1 ≤ ℓ → 1 ≤ r → ℓ ≤ k → r ≤ k → 0 < ε → ε ≤ 1 / 2 →
        0 < δ → δ ≤ 1 / 2 →
        ∀ (α : Fin ℓ → ℂ) (f' : Fin ℓ → ℝ) (β : Fin r → ℂ) (f : Fin r → ℝ),
          (∀ i j, min (constCH C * ((ℓ : ℝ) * r / δ) *
              (Real.logb 2 ((ℓ : ℝ) * r / δ) + Real.logb 2 ((k : ℝ) / ε)))
              (2 * filterDelta C k ε) ≤ |f i - f' j|) →
          Integrable (fun t => filtered C k k ε (sparseSignal α f') t *
            (starRingEnd ℂ) (filtered C k k ε (sparseSignal β f) t)) ∧
          ‖linner (filtered C k k ε (sparseSignal α f')) (filtered C k k ε (sparseSignal β f))‖ₑ ^ 2
            ≤ ENNReal.ofReal (δ ^ 2) * lsq (filtered C k k ε (sparseSignal α f')) *
                lsq (filtered C k k ε (sparseSignal β f))) := by sorry

end CaiFourierSparse.Learning
