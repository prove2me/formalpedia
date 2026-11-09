-- Prove2me | Theorems.Thm_CliffordCert_Optimal_spectral_estimator
-- name    : CliffordCert.Optimal.spectral_estimator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:58.538905+00:00
-- url     : https://prove2.me/theorems/c17f8add-98e2-4030-9a7e-30075bc8e3d6
-- title:
--   Lemma 10 — spectral estimator mean and variance
-- statement:
--   Let $\omega,\tau$ be arbitrary $r$-dimensional density matrices, $r\ge1$, and let $s\ge2$. Measure the spectral projections of the actual matrix $T_s(\tau)$ of Eq. (4) in state $\omega^{\otimes s}$ and report its eigenvalue $Z$. With $D=\|\omega-\tau\|_2^2$,
--   $$\mathbb EZ=D,\qquad\operatorname{Var}Z\le\frac{4D}s+\frac{32}{s(s-1)}\le\frac{4D}s+\frac{64}{s^2}.$$
--   The statement also asserts Hermiticity, positivity and completeness of the projections and normalization of the Born law. It uses finite spectral sums, so it needs no integrability assumption and allows negative eigenvalues.
--
--   This supplies the quantitative estimator needed for both certification promises.
--
--   Differences from the source:
--   - encoding: the spectral outcome law of Eq. (4) → rank-one eigenbasis projections with equal eigenvalues reported identically, and explicit finite Born sums; reason: summing the weights for a repeated eigenvalue gives its eigenspace spectral probability
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 16, Lemma 10, Eq. (27) (PDF p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_spectral_protocol
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem spectral_estimator (r s : ℕ) (hr : 1 ≤ r) (hs : 2 ≤ s)
    (ω τ : Mat (Fin r)) (hω : IsState ω) (hτ : IsState τ) :
    let A := distanceObservable τ s
    let ρ := tensorPower ω s
    let D := hsSq (ω - τ)
    A.IsHermitian ∧
    (∀ j, (spectralProjection A j).PosSemidef) ∧
    (∑ j, spectralProjection A j) = 1 ∧
    (∀ j, 0 ≤ spectralWeight A ρ j) ∧
    (∑ j, spectralWeight A ρ j) = 1 ∧
    spectralMean A ρ = D ∧
    spectralVariance A ρ ≤ 4*D/(s : ℝ) + 32/((s : ℝ)*(s-1 : ℕ)) ∧
    4*D/(s : ℝ) + 32/((s : ℝ)*(s-1 : ℕ)) ≤ 4*D/(s : ℝ) + 64/(s : ℝ)^2 := by sorry
end CliffordCert.Optimal
