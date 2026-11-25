-- Prove2me | Theorems.Thm_Arxiv0812_1178_cartesian_moments_scalar_case
-- name    : Arxiv0812_1178.cartesian_moments_scalar_case
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T08:56:02.396832+00:00
-- url     : https://prove2.me/theorems/9d5b4f67-08ee-4218-8547-72e89daa0c19
-- title:
--   Appendix E.C, eq. (59): the scalar (decorrelated) case
-- statement:
--   In the setting of eq. (58), suppose in addition that the noise components are decorrelated: $R_a=\operatorname{Diag}(\sigma_{a,i}^2)$ and $R_\phi=\operatorname{Diag}(\sigma_{\phi,i}^2)$, with $a^{noise}$ and $\phi^{noise}$ independent Gaussian vectors. Then the radial and tangential covariances are diagonal and the cross-covariance vanishes: $R_{rad,rad}=\operatorname{Diag}(\sigma_{rad,i}^2)$, $R_{tan,tan}=\operatorname{Diag}(\sigma_{tan,i}^2)$ and $R_{rad,tan}=0$, where
--   $$\sigma_{rad,i}^2=\frac{\bar a_i^2}{2}\big(1-e^{-\sigma_{\phi,i}^2}\big)^2+\frac{\sigma_{a,i}^2}{2}\big(1+e^{-2\sigma_{\phi,i}^2}\big),$$
--   $$\sigma_{tan,i}^2=\frac{\bar a_i^2}{2}\big(1-e^{-2\sigma_{\phi,i}^2}\big)+\frac{\sigma_{a,i}^2}{2}\big(1-e^{-2\sigma_{\phi,i}^2}\big).$$
--
--   These variances give the elliptic contours of the Cartesian approximation (Fig. 1).
--
--   **Formalization Note** As for eq. (58), "decorrelated" between the amplitude and phase noises is read as independence of the two Gaussian vectors.
-- source:
--   Meimon, Mugnier and Le Besnerais, A self-calibration approach for optical long baseline interferometry imaging, arXiv:0812.1178v1 (2008), claim c016; Appendix E.C 'The scalar case', eq. (59), PDF pp. 22-23

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv0812_1178

theorem cartesian_moments_scalar_case {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (abar phibar : ι → ℝ)
    (σa σφ : ι → ℝ)
    (anoise phinoise : Ω → EuclideanSpace ℝ ι) (ham : Measurable anoise)
    (hφm : Measurable phinoise)
    (hag : Pr.map anoise = multivariateGaussian 0 (Matrix.diagonal fun i => σa i ^ 2))
    (hφg : Pr.map phinoise = multivariateGaussian 0 (Matrix.diagonal fun i => σφ i ^ 2))
    (hind : IndepFun anoise phinoise Pr) :
    (∀ i j, covariance
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr =
      if i = j then
        abar i ^ 2 / 2 * (1 - Real.exp (-(σφ i ^ 2))) ^ 2 +
          σa i ^ 2 / 2 * (1 + Real.exp (-(2 * σφ i ^ 2)))
      else 0) ∧
    (∀ i j, covariance
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr =
      if i = j then
        abar i ^ 2 / 2 * (1 - Real.exp (-(2 * σφ i ^ 2))) +
          σa i ^ 2 / 2 * (1 - Real.exp (-(2 * σφ i ^ 2)))
      else 0) ∧
    (∀ i j, covariance
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr = 0) := by sorry

end Arxiv0812_1178
