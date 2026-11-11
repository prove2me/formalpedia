-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_lemma_6_3
-- name    : CaiFourierSparse.Learning.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:14:44.650237+00:00
-- url     : https://prove2.me/theorems/5161d559-b24b-4c21-bf5a-24fb0d7817c9
-- title:
--   Lemma 6.3 — the filter $M_{\ell,\delta}$: $\|M x-x\|^2\le\frac\delta2\|x\|^2$, energy concentration, and Fourier support within $\Delta_{\ell,\delta}$
-- statement:
--   Let $C\ge64$ be even, $\ell\ge1$ and $0<\delta\le1/2$. For every $\ell$-Fourier-sparse $x$, the filter $M_{\ell,\delta}=M_{\ell,\ell,\delta}$ satisfies
--   1. in the time domain, $\|M_{\ell,\delta}x-x\|^2_{[-1,1]}\le\frac\delta2\|x\|^2_{[-1,1]}$ and $\|M_{\ell,\delta}x\|^2_{[-1,1]}\ge(1-\delta)\|M_{\ell,\delta}x\|_2^2$;
--   2. in the frequency domain, $M_{\ell,\delta}x$ is integrable and $\operatorname{supp}\widehat{M_{\ell,\delta}x}\subseteq\bigcup_{f_j\in\operatorname{supp}(\hat x)}[f_j-\Delta_{\ell,\delta},f_j+\Delta_{\ell,\delta}]$, $\Delta_{\ell,\delta}=C_M\frac{\ell^2}\delta\log\frac\ell\delta$.
--
--   Differences from the source:
--   - reading: C ≥ 64 an even integer (§6), C_M a universal constant with Δ_M = (C_M/2)(…) in (67) → every even C ≥ 64, with C_M = 4C² and C_H = 8C_M; reason: Claim 6.5(5) bounds the same radius Δ_M by 2C²(…), so C_M/2 = 2C²; quantifying over every admissible C is the strongest reading
--   - reading: log in the filter constants Δ_{ℓ,δ}, d_min and in the separation thresholds → base-2 logarithm; reason: the Fourier transform of (72) prints ⌈log₂ r⌉; the base of the filter's exponents must be fixed for the objects to be defined
--   - encoding: given any ℓ and δ → ℓ ≥ 1 and 0 < δ ≤ 1/2; reason: the section's standing assumptions for the construction (Claim 6.5, Lemma 6.1); ℓ = 0 is an empty signal
--   - encoding: supp of the Fourier transform of M_{ℓ,δ}·x → M_{ℓ,δ}·x is integrable (an added clause) and its Fourier integral is nonzero only within Δ_{ℓ,δ} of a frequency of supp(x̂) (cancelling or zero amplitudes excluded); reason: the added integrability makes the Fourier transform the paper's integral rather than a junk 0
--   - encoding: squared L² norms → ℝ≥0∞-valued lower integrals wsq/lsq/osq, real coefficients through ENNReal.ofReal; reason: non-square-integrable functions get energy ∞, so no bound holds through a junk value
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Lemma 6.3, printed p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_Filter

namespace CaiFourierSparse.Learning

open MeasureTheory

/-- Lemma 6.3 (printed p. 32, PDF p. 34). Let `C ≥ 64` be an even integer, `ℓ ≥ 1` and
`0 < δ ≤ 1/2`. The filter `M_{ℓ,δ} = M_{ℓ,ℓ,δ}` satisfies, for every `ℓ`-Fourier-sparse `x`:
(1) `‖M_{ℓ,δ} x - x‖²_{[-1,1]} ≤ (δ/2) ‖x‖²_{[-1,1]}` and
`‖M_{ℓ,δ} x‖²_{[-1,1]} ≥ (1 - δ) ‖M_{ℓ,δ} x‖²₂`;
(2) `M_{ℓ,δ} x` is integrable and its Fourier transform vanishes outside
`⋃_{f_j ∈ supp(x̂)} [f_j - Δ_{ℓ,δ}, f_j + Δ_{ℓ,δ}]`, `Δ_{ℓ,δ} = C_M (ℓ²/δ) log(ℓ/δ)`. -/
theorem lemma_6_3 (C : ℕ) (hCe : Even C) (hC : 64 ≤ C) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (δ : ℝ)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (α : Fin ℓ → ℂ) (f : Fin ℓ → ℝ) :
    wsq (fun t => filtered C ℓ ℓ δ (sparseSignal α f) t - sparseSignal α f t) ≤
        ENNReal.ofReal (δ / 2) * wsq (sparseSignal α f) ∧
      ENNReal.ofReal (1 - δ) * lsq (filtered C ℓ ℓ δ (sparseSignal α f)) ≤
        wsq (filtered C ℓ ℓ δ (sparseSignal α f)) ∧
      Integrable (filtered C ℓ ℓ δ (sparseSignal α f)) ∧
      ∀ ξ : ℝ, ftR (filtered C ℓ ℓ δ (sparseSignal α f)) ξ ≠ 0 →
        ∃ g ∈ specSupp α f, |ξ - g| ≤ filterDelta C ℓ δ := by sorry

end CaiFourierSparse.Learning
