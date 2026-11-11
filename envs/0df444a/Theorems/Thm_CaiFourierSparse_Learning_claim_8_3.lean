-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_claim_8_3
-- name    : CaiFourierSparse.Learning.claim_8_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:17:44.275194+00:00
-- url     : https://prove2.me/theorems/8e7b8b6b-2756-4d48-9d27-32bc5d5c0b76
-- title:
--   Claim 8.3 — the scans of Algorithm 3: $|I'|\le\sum_i|[\ell_i,r_i]|+2\sum_im_i/\tau$, and local spectral energy $\lesssim\tau r$ off $I'$
-- statement:
--   There is a constant $A$ such that for every Haar–Fourier expansion $\tilde x=\sum_H\beta_H\varphi_H$ over $\mathcal H_{2N}$ (each $H$ once) and every $\tau>0$, the set $I'=\bigcup_i[L_i,R_i]$ returned by Algorithm 3's scans from the merged regions $[\ell_i,r_i]$ with energies $m_i$ satisfies
--   $$|I'|\le\sum_i|[\ell_i,r_i]|+\frac{2\sum_im_i}\tau\qquad\text{(eq. (82))},$$
--   and for every $f_0\notin I'$ and $r\ge1$, $\sum_{n:|n/2-f_0|\le r}|\hat{\tilde x}[n]|^2\le A\tau r$ (eq. (83)).
--
--   Differences from the source:
--   - encoding: I′ returned by Algorithm 3 → coverWithTau b a terms τ = some I (the scans with the given τ); no output when there is no nonzero coefficient; reason: Algorithm 3 has no branch for an empty region list (INSIGHTS I2); the claim concerns returned covers
--   - encoding: x̃ from ImproperLearning → any expansion over H_{2N} (N = 2^b, K = 2^a, a ≤ b + 1) using each H at most once; reason: Algorithm 1 sets one β_H per H; the claim's proof uses nothing else
--   - encoding: |I′| → Lebesgue measure of ⋃_i [L_i, R_i]; reason: I′ is a union of possibly overlapping intervals; its size is the measure of the union
--   - encoding: ≲ → ≤ A·τ·r with A > 0 fixed before all data; reason: the paper's ≲ hides a universal constant (the proof gives 2τr)
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Claim 8.3, printed p. 41 (PDF p. 43)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_HaarFourier
import Definitions.Def_CaiFourierSparse_Learning_Cover

namespace CaiFourierSparse.Learning

open MeasureTheory

/-- Claim 8.3 (printed p. 41, PDF p. 43). There is a constant `A` such that for every
Haar–Fourier expansion `x̃ = ∑_H β_H φ_H` over `H_{2N}` (`N = 2^b`, `K = 2^a`, `K ∣ 2N`, each `H`
once) and every `τ > 0`, the cover `I' = ⋃_i [L_i, R_i]` returned by the scans of Algorithm 3
from the merged regions `[ℓ_i, r_i]` with energies `m_i` satisfies
`|I'| ≤ ∑_i |[ℓ_i, r_i]| + 2 ∑_i m_i / τ` (eq. (82)), and for every `f₀ ∉ I'` and `r ≥ 1`,
`∑_{n : |n/2 - f₀| ≤ r} |x̃̂[n]|² ≤ A τ r` (eq. (83)). -/
theorem claim_8_3 :
    ∃ A : ℝ, 0 < A ∧
      ∀ (b a : ℕ) (terms : List (HaarIdx × ℂ)), a ≤ b + 1 →
        (∀ p ∈ terms, p.1 ∈ haarIdxSet b a) → (terms.map Prod.fst).Nodup →
        ∀ τ : ℝ, 0 < τ → ∀ I : List (ℝ × ℝ), coverWithTau b a terms τ = some I →
          volume (ivUnion I) ≤
            ENNReal.ofReal (((mergedRegions b a terms).map fun z => z.2.1 - z.1).sum +
              2 * ((mergedRegions b a terms).map fun z => z.2.2).sum / τ) ∧
          ∀ f₀ : ℝ, f₀ ∉ ivUnion I → ∀ r : ℝ, 1 ≤ r →
            ∑ n ∈ Finset.Icc (Int.ceil (2 * (f₀ - r))) (Int.floor (2 * (f₀ + r))),
              ‖fsc (hfSum b a terms) n‖ ^ 2 ≤ A * τ * r := by sorry

end CaiFourierSparse.Learning
