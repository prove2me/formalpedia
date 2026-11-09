-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_lemma_3_16
-- name    : BLTCounting.AccuracySpace.lemma_3_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:42.488831+00:00
-- url     : https://prove2.me/theorems/f29bd221-b14a-446f-9868-93e462b348d0
-- title:
--   Counting large band-matrix eigenvalues
-- statement:
--   Let $B$ be the $K\times K$ band matrix with $0<\theta\le\pi$, with eigenvalues $\lambda_1\ge\dots\ge\lambda_K$, and let $q=\#\{j:\lambda_j\ge1/2\}$. Then
--   $$q\ge\frac{K\theta}\pi-O(\log(K\theta))\qquad(K\theta\to\infty),$$
--   with an implied constant uniform in $K$ and $\theta$. This count supplies the main term of the lower bound on the recurrence order.
--
--   **Formalization Note.** The threshold is $\ge1/2$, not $>1/2$. Hermitian-ness of $B$ is part of the conclusion, since the eigenvalue count requires it.
--
--   Differences from the source:
--   - generalization: the threshold $\theta_*=h\omega_*$ of the respective section → every $\theta$ with $0<\theta\le\pi$; reason: the proof uses only $[-\theta_*,\theta_*]\subseteq[-\pi,\pi]$; the source statement is the special case
--   - reading: $O(\log(K\theta_*))$ with no stated regime → an absolute constant $C$ and a threshold $X_0$, valid for $K\theta\ge X_0$, uniform in $K$ and $\theta$; reason: $\log(K\theta)$ is not positive for small $K\theta$; the source applies the bound as $K\theta_*\to\infty$
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 3.16, printed p. 23 (PDF p. 24)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

open Matrix

namespace BLTCounting.AccuracySpace

/-- Lemma 3.16, PDF p. 24: with `q = #{j : λ_j(B) ≥ 1/2}`, one has `q ≥ Kθ/π - O(log(Kθ))` as
`Kθ → ∞`, with a constant uniform in `K` and `θ ∈ (0, π]`. -/
theorem lemma_3_16 :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ (K : ℕ) (θ : ℝ), 0 < θ → θ ≤ Real.pi → X₀ ≤ (K : ℝ) * θ →
      ∃ hB : (bandMatrix K θ).IsHermitian,
        (K : ℝ) * θ / Real.pi - C * Real.log ((K : ℝ) * θ) ≤
          (eigCountAtLeast hB (1 / 2) : ℝ) := by sorry

end BLTCounting.AccuracySpace
