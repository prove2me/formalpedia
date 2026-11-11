-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_claim_5_2
-- name    : CaiFourierSparse.Learning.claim_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:15:23.0143+00:00
-- url     : https://prove2.me/theorems/a45a7d5c-14f3-4ab4-954f-05deaca38bb6
-- title:
--   Claim 5.2 — sparse truncation of Haar–Fourier coefficients (strict inequality as printed)
-- statement:
--   For every $k$-Fourier-sparse $x$ with frequencies in $[-F,F]$, the Haar–Fourier basis $\mathcal B$ ($N=2^b\ge2F$, $K=2^a\ge k$, $K\mid2N$), $P_Nx=\sum_H\alpha_H\varphi_H$ and every positive integer $s$, the top-$s$ coefficients approximate $P_Nx$ with error
--   $$\|\mathrm{bottom}_s(\alpha_H)\|_2^2<C\,\frac{k\log^2(Nk)}{s}\,\|P_Nx\|^2_{[-1,1]}$$
--   for one universal constant $C>0$. The strict inequality is stated as printed; it fails for $x=0$ (INSIGHTS I1).
--
--   Differences from the source:
--   - encoding: integer s → s ≥ 1; reason: 'the top s functions' and the division by s need a positive integer; s = 0 is undefined
--   - encoding: O(k log²(Nk)/s) → C·k·log²(Nk)/s with C > 0 fixed before all parameters; reason: the O-constant is universal
--   - encoding: ‖bottom_s(α_H)‖²₂ (erase the s largest entries) → the minimum over erased sets of size ≤ s (bottomSq), compared in ℝ≥0∞; reason: the same number for every tie-breaking
--   - encoding: P_N x := Σ_H α_H φ_H → projN (the Fourier sum (15)); reason: equal by Fact 4.2
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Claim 5.2, printed p. 25 (PDF p. 27)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_HaarFourier

namespace CaiFourierSparse.Learning

/-- Claim 5.2 (printed p. 25, PDF p. 27), with the printed strict inequality. For every
`k`-Fourier-sparse `x` and every positive integer `s`, the coefficient vector `α_H = ⟨x, φ_H⟩`
over the Haar–Fourier basis `B` (`N = 2^b ≥ 2F`, `K = 2^a ≥ k`, `K ∣ 2N`) satisfies
`‖bottom_s(α_H)‖²₂ < C (k log²(Nk)/s) ‖P_N x‖²_{[-1,1]}` for one universal constant `C`. -/
theorem claim_5_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : ℝ) (k a b s : ℕ), 0 ≤ F → 1 ≤ k → k ≤ 2 ^ a → 2 * F ≤ 2 ^ b → a ≤ b + 1 → 1 ≤ s →
        ∀ (α : Fin k → ℂ) (f : Fin k → ℝ), Bandlimited F f →
          ENNReal.ofReal (bottomSq (hfCoeff b a (sparseSignal α f)) (haarIdxSet b a) s) <
            ENNReal.ofReal (C * k * Real.log ((2 : ℝ) ^ b * k) ^ 2 / s) *
              wsq (projN (2 ^ b) (sparseSignal α f)) := by sorry

end CaiFourierSparse.Learning
