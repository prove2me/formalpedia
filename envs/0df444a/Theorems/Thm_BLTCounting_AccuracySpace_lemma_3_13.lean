-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_lemma_3_13
-- name    : BLTCounting.AccuracySpace.lemma_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:41.226687+00:00
-- url     : https://prove2.me/theorems/67058f79-7e53-46fc-8a52-1174ae3dc932
-- title:
--   Spectral and trace properties of the band matrix
-- statement:
--   Let $0<\theta\le\pi$, and let $B$ be the $K\times K$ band matrix with coefficients $b_0=\theta/\pi$, $b_p=\sin(p\theta)/(\pi p)$. Then:
--
--   1. $0\preceq B\preceq I$;
--   2. $\mathrm{Tr}(B)=K\theta/\pi=Kb_0$ and $\sum_{p\in\mathbb Z}|b_p|^2=b_0$;
--   3. $\mathrm{Tr}(B^2)=K|b_0|^2+2\sum_{p=1}^{K-1}(K-p)|b_p|^2$.
--
--   These identities prepare the count of large eigenvalues of $B$.
--
--   Differences from the source:
--   - generalization: the threshold $\theta_*=h\omega_*$ of the respective section → every $\theta$ with $0<\theta\le\pi$; reason: the proof uses only $[-\theta_*,\theta_*]\subseteq[-\pi,\pi]$; the source statement is the special case
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 3.13, printed p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

open Matrix
open scoped ComplexOrder

namespace BLTCounting.AccuracySpace

/-- Lemma 3.13, PDF p. 22: for `0 < θ ≤ π`, the `K × K` band matrix `B` satisfies
(1) `0 ⪯ B ⪯ I`; (2) `Tr(B) = Kθ/π = K b₀` and `∑_{p ∈ ℤ} |b_p|² = b₀`;
(3) `Tr(B²) = K |b₀|² + 2 ∑_{p=1}^{K-1} (K - p) |b_p|²`. -/
theorem lemma_3_13 (K : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi) :
    ((bandMatrix K θ).PosSemidef ∧ (1 - bandMatrix K θ).PosSemidef) ∧
      ((bandMatrix K θ).trace = (((K : ℝ) * θ / Real.pi : ℝ) : ℂ) ∧
        (bandMatrix K θ).trace = (((K : ℝ) * bandCoeff θ 0 : ℝ) : ℂ) ∧
        HasSum (fun p : ℤ => |bandCoeff θ p| ^ 2) (bandCoeff θ 0)) ∧
      (bandMatrix K θ * bandMatrix K θ).trace =
        (((K : ℝ) * |bandCoeff θ 0| ^ 2 +
          2 * ∑ p ∈ Finset.Ico 1 K, ((K : ℝ) - p) * |bandCoeff θ (p : ℤ)| ^ 2 : ℝ) : ℂ) := by sorry

end BLTCounting.AccuracySpace
