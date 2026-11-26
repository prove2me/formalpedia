-- Prove2me | Theorems.Thm_CondMat0408017_rms_height_difference_topothesy
-- name    : CondMat0408017.rms_height_difference_topothesy
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-26T13:19:19.969864+00:00
-- url     : https://prove2.me/theorems/1d49b81a-dbdd-5c13-8acc-1d78ffa23cac
-- title:
--   Eq. (38): rms height difference of a self-affine profile, $\sigma(\Delta x_1)=\ell^{1-H}\Delta x_1^H$
-- statement:
--   Let $\zeta(x_1)$ be a random surface profile on a probability space, with stationary increments: the law of $\zeta(x+\Delta)-\zeta(x)$ does not depend on $x$. Let it be statistically self-affine with Hurst exponent $H$ between the scales $0\le\xi_-<\xi_+$ (eq. 35): for $\lambda>0$ and $\Delta,\lambda\Delta\in(\xi_-,\xi_+)$, $\zeta(\Delta)-\zeta(0)$ has the same law as $\lambda^{-H}(\zeta(\lambda\Delta)-\zeta(0))$. Let the topothesy $\ell\in(\xi_-,\xi_+)$ satisfy $\sigma(\ell)=\ell$, where $\sigma(\Delta x_1)=\langle(\zeta(x_1+\Delta x_1)-\zeta(x_1))^2\rangle^{1/2}$ (eqs. 36-37). Then for every $x_1$ and every $\Delta x_1\in(\xi_-,\xi_+)$
--
--   $$\sigma(\Delta x_1)=\ell^{1-H}\,\Delta x_1^{H} .$$
--
--   **Formalization Note** The paper's average $\langle\cdot\rangle_{x_1}$ over positions is taken as an ensemble average, and stationarity of increments makes it independent of $x_1$. "Statistically invariant" (eq. 35) is equality in law of the increments at the scales of the self-affine window. The topothesy is assumed to lie in the window, which is where $\sigma(x)\sim x^H$ is available. The paper notes that $\ell$ need not lie there in general.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c004; Sec. II.G, eq. (Eq:sigma) [(38)] from eqs. (Eq:CHAR:Scaling-rel), (Eq:CHAR:rms-top), (Eq:CHAR:Topothesy), PDF p. 15

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem rms_height_difference_topothesy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ζ : ℝ → Ω → ℝ) (H ξm ξp ℓ : ℝ) (hξm : 0 ≤ ξm)
    (hstat : ∀ x Δ : ℝ,
      ProbabilityTheory.IdentDistrib (fun w => ζ (x + Δ) w - ζ x w) (fun w => ζ Δ w - ζ 0 w) P P)
    (hsa : ∀ Δ l : ℝ, 0 < l → Δ ∈ Set.Ioo ξm ξp → l * Δ ∈ Set.Ioo ξm ξp →
      ProbabilityTheory.IdentDistrib (fun w => ζ Δ w - ζ 0 w) (fun w => l ^ (-H) * (ζ (l * Δ) w - ζ 0 w)) P P)
    (hℓ : ℓ ∈ Set.Ioo ξm ξp) (h37 : rmsHeightDiff P ζ ℓ = ℓ) :
    ∀ x Δ : ℝ, Δ ∈ Set.Ioo ξm ξp →
      Real.sqrt (∫ w, (ζ (x + Δ) w - ζ x w) ^ 2 ∂P) = ℓ ^ (1 - H) * Δ ^ H := by sorry

end CondMat0408017
