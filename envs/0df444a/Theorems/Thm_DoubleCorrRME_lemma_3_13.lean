-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_3_13
-- name    : DoubleCorrRME.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:20.978198+00:00
-- url     : https://prove2.me/theorems/064739b5-8e82-4258-9b21-233426cc239e
-- title:
--   Lemma 3.13, p.19 — MMW covariance contraction: $\|M^{(T)}\|_2\le\Lambda_0/2$
-- statement:
--   Let $d\ge1$ and $M^{(0)}\succeq\cdots\succeq M^{(T)}\succeq0$ be PSD matrices with $\Lambda_0=\|M^{(0)}\|_2>0$, and let $0\le\nu\le1/40$. Let $\Psi^{(r)}$ be the MMW density (epoch start $0$) with gains $F^{(r)}=M^{(r+1)}$ and learning rate $\eta$ with
--
--   $$\frac{1-\nu}{1+\nu}\le\eta\Lambda_0\le1 .$$
--
--   If $\langle\Psi^{(r)},M^{(r+1)}\rangle\le\Lambda_0/6$ for every $r<T$ and $T\ge8\log(2d)$, then
--
--   $$\|M^{(T)}\|_2\le\Lambda_0/2 .$$
--
--   This is why every epoch of the sample-level filter halves the weighted covariance.
--
--   Differences from the source:
--   - reading: ν ≤ 1/40 → 0 ≤ ν ≤ 1/40; reason: ν is the approximation parameter of Definition 3.9 (ν ∈ (0, 1/20)); for ν < −1 the hypotheses allow η → 0, Ψ ≈ I/d, and a constant rank-one M with d ≥ 6 violates the conclusion
--   - encoding: matrices in ℝ^{d×d}, MMW density of Definition 3.7 → 1 ≤ d, epoch start t₀ = 0, Ψ^(r) = mmwDensity η (s ↦ M^(s+1)) 0 r; reason: d = 0 has no density matrix; the lemma's gains start at r = 0
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 3.13, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Weights

namespace DoubleCorrRME

/-- **Lemma 3.13** (MMW covariance contraction), p.19 (PDF p.20).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Let M^(0) ⪰ ⋯ ⪰ M^(T) ⪰ 0 be PSD matrices, Λ_0 := ∥M^(0)∥₂ > 0, and ν ≤ 1/40. Let Ψ^(r) be the MMW
density with gains F^(r) = M^(r+1) and a learning rate satisfying (1 − ν)/(1 + ν) ≤ ηΛ_0 ≤ 1. If
⟨Ψ^(r), M^(r+1)⟩ ≤ Λ_0/6 for every r < T, and T ≥ 8 log(2d), then ∥M^(T)∥₂ ≤ Λ_0/2."

**Formalization Note.**
* `ν` is the approximation parameter of Definition 3.9, so `ν ≥ 0`; the lemma reads
  `0 ≤ ν ≤ 1/40`. (For `ν < −1` the hypotheses allow `η → 0`, `Ψ ≈ I/d`, and a constant rank-one
  `M` with `d ≥ 6` violates the conclusion.)
* `d ≥ 1`; the epoch starts at `t₀ = 0`, so `Ψ^(r) = mmwDensity η (s ↦ M^(s+1)) 0 r`.
* `A ⪰ B` is `(A − B).PosSemidef`; `∥·∥₂` is the spectral norm `opNorm`; `⟨·,·⟩` is the Frobenius
  inner product. -/
theorem lemma_3_13 :
    ∀ (d : ℕ), 1 ≤ d → ∀ (T : ℕ) (M : ℕ → Matrix (Fin d) (Fin d) ℝ) (ν η : ℝ),
      (∀ r < T, (M r - M (r + 1)).PosSemidef) → (M T).PosSemidef →
      0 < HighDimProb.QuadraticForms.opNorm (M 0) →
      0 ≤ ν → ν ≤ 1 / 40 →
      (1 - ν) / (1 + ν) ≤ η * HighDimProb.QuadraticForms.opNorm (M 0) →
      η * HighDimProb.QuadraticForms.opNorm (M 0) ≤ 1 →
      (∀ r < T, frobInner (mmwDensity η (fun s => M (s + 1)) 0 r) (M (r + 1)) ≤
        HighDimProb.QuadraticForms.opNorm (M 0) / 6) →
      8 * Real.log (2 * (d : ℝ)) ≤ T →
      HighDimProb.QuadraticForms.opNorm (M T) ≤
        HighDimProb.QuadraticForms.opNorm (M 0) / 2 := by sorry

end DoubleCorrRME
