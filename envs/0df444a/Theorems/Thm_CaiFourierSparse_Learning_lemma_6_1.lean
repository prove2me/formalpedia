-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_lemma_6_1
-- name    : CaiFourierSparse.Learning.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:14:45.760211+00:00
-- url     : https://prove2.me/theorems/f93c355d-6c32-44e5-90e3-29008caed1e5
-- title:
--   Lemma 6.1 — frequency separation $C_M(\frac\ell\delta\min\{r,\frac\ell\delta\}\log\frac{\ell r}\delta+\frac{\ell r}\delta)$ gives $|\langle w,z\rangle|\le\delta\|w\|\|z\|$
-- statement:
--   Let $0<\delta\le1/2$ and $C_M$ the constant of (67). For an $\ell$-Fourier-sparse $w=\sum_{j<\ell}\alpha_je^{2\pi if'_jt}$ and an $r$-Fourier-sparse $z=\sum_{j<r}\beta_je^{2\pi if_jt}$, if
--   $$\min_{i,j}|f_i-f'_j|>C_M\Big(\frac\ell\delta\min\Big\{r,\frac\ell\delta\Big\}\log\frac{\ell r}\delta+\frac{\ell r}\delta\Big),$$
--   then $|\langle w,z\rangle_{[-1,1]}|\le\delta\|w\|_{[-1,1]}\|z\|_{[-1,1]}$ (eq. (66)).
--
--   Differences from the source:
--   - reading: C ≥ 64 an even integer (§6), C_M a universal constant with Δ_M = (C_M/2)(…) in (67) → every even C ≥ 64, with C_M = 4C² and C_H = 8C_M; reason: Claim 6.5(5) bounds the same radius Δ_M by 2C²(…), so C_M/2 = 2C²; quantifying over every admissible C is the strongest reading
--   - reading: log in the filter constants Δ_{ℓ,δ}, d_min and in the separation thresholds → base-2 logarithm; reason: the Fourier transform of (72) prints ⌈log₂ r⌉; the base of the filter's exponents must be fixed for the objects to be defined
--   - encoding: |⟨w,z⟩| ≤ δ‖w‖‖z‖ → |⟨w,z⟩|² ≤ δ²‖w‖²‖z‖² (energies in ℝ≥0∞); reason: equivalent for δ > 0
--   - encoding: min_{i,j}|f_i − f'_j| > threshold → |f_i − f'_j| > threshold for all i, j; reason: equivalent
--   - encoding: sparsities ℓ and r → ℓ, r ≥ 1; reason: log(ℓr/δ) needs ℓr > 0; an empty signal makes the claim trivial
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Lemma 6.1, printed p. 31 (PDF p. 33)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_Filter

namespace CaiFourierSparse.Learning

/-- Lemma 6.1 (printed p. 31, PDF p. 33). Let `C ≥ 64` be an even integer, `C_M = 4C²` the
constant of (67), and `0 < δ ≤ 1/2`. For an `ℓ`-Fourier-sparse `w = ∑_{j<ℓ} α_j e^{2π i f'_j t}`
and an `r`-Fourier-sparse `z = ∑_{j<r} β_j e^{2π i f_j t}`, if
`min_{i,j} |f_i - f'_j| > C_M ((ℓ/δ) · min{r, ℓ/δ} · log(ℓr/δ) + ℓr/δ)` then
`|⟨w, z⟩_{[-1,1]}| ≤ δ ‖w‖_{[-1,1]} ‖z‖_{[-1,1]}` (stated squared). -/
theorem lemma_6_1 (C : ℕ) (hCe : Even C) (hC : 64 ≤ C) (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (ℓ r : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r) (α : Fin ℓ → ℂ) (f' : Fin ℓ → ℝ)
    (β : Fin r → ℂ) (f : Fin r → ℝ)
    (hsep : ∀ i j, constCM C * (((ℓ : ℝ) / δ) * min (r : ℝ) ((ℓ : ℝ) / δ) *
        Real.logb 2 ((ℓ : ℝ) * r / δ) + (ℓ : ℝ) * r / δ) < |f i - f' j|) :
    ‖winner (sparseSignal α f') (sparseSignal β f)‖ₑ ^ 2 ≤
      ENNReal.ofReal (δ ^ 2) * wsq (sparseSignal α f') * wsq (sparseSignal β f) := by sorry

end CaiFourierSparse.Learning
