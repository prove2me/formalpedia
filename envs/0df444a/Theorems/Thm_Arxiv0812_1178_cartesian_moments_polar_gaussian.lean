-- Prove2me | Theorems.Thm_Arxiv0812_1178_cartesian_moments_polar_gaussian
-- name    : Arxiv0812_1178.cartesian_moments_polar_gaussian
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T08:54:48.115825+00:00
-- url     : https://prove2.me/theorems/2f26f823-0250-4e30-845a-e4578024a172
-- title:
--   Appendix E.B, eq. (58): mean and covariance of the radial and tangential noise
-- statement:
--   Let $\bar a,\bar\phi$ be real vectors indexed by a finite set. Let $a^{noise}\sim\mathcal N(0,R_a)$ and $\phi^{noise}\sim\mathcal N(0,R_\phi)$ be independent Gaussian random vectors. Set $a^{data}=\bar a+a^{noise}$, $\phi^{data}=\bar\phi+\phi^{noise}$, $y^{noise}=a^{data}e^{i\phi^{data}}-\bar ae^{i\bar\phi}$, and
--   $$y^n_{rad}=\operatorname{Re}(y^{noise}e^{-i\bar\phi}),\qquad y^n_{tan}=\operatorname{Im}(y^{noise}e^{-i\bar\phi}).$$
--   Then for all indices $i,j$, writing $E_{ij}=e^{-(R_{\phi,ii}+R_{\phi,jj})/2}$:
--   $$\mathbb E\,y^n_{rad,i}=\bar a_i\big(e^{-R_{\phi,ii}/2}-1\big),\qquad\mathbb E\,y^n_{tan,i}=0,$$
--   $$\operatorname{Cov}(y^n_{rad,i},y^n_{rad,j})=\big[\bar a_i\bar a_j(\cosh R_{\phi,ij}-1)+R_{a,ij}\cosh R_{\phi,ij}\big]E_{ij},$$
--   $$\operatorname{Cov}(y^n_{rad,i},y^n_{tan,j})=0,\qquad\operatorname{Cov}(y^n_{tan,i},y^n_{tan,j})=(\bar a_i\bar a_j+R_{a,ij})\sinh R_{\phi,ij}\,E_{ij}.$$
--
--   These are the mean and covariance of the Cartesian Gaussian approximation of a polar Gaussian noise model.
--
--   **Formalization Note** The paper says that $a^{noise}$ and $\phi^{noise}$ are "uncorrelated". Here they are independent, which is the same thing when $(a^{noise},\phi^{noise})$ is jointly Gaussian. Without joint Gaussianity, uncorrelatedness is not enough for eq. (58) (see the mission report).
-- source:
--   Meimon, Mugnier and Le Besnerais, A self-calibration approach for optical long baseline interferometry imaging, arXiv:0812.1178v1 (2008), claim c015; Appendix E.A, eqs. (52)-(55), PDF pp. 21-22; Appendix E.B, eqs. (56)-(58), PDF p. 22

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv0812_1178

theorem cartesian_moments_polar_gaussian {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (abar phibar : ι → ℝ)
    (Ra Rφ : Matrix ι ι ℝ) (hRa : Ra.PosSemidef) (hRφ : Rφ.PosSemidef)
    (anoise phinoise : Ω → EuclideanSpace ℝ ι) (ham : Measurable anoise)
    (hφm : Measurable phinoise) (hag : Pr.map anoise = multivariateGaussian 0 Ra)
    (hφg : Pr.map phinoise = multivariateGaussian 0 Rφ) (hind : IndepFun anoise phinoise Pr) :
    (∀ i, ∫ ω, radNoise abar phibar (fun j => anoise ω j) (fun j => phinoise ω j) i ∂Pr =
      abar i * (Real.exp (-(Rφ i i / 2)) - 1)) ∧
    (∀ i, ∫ ω, tanNoise abar phibar (fun j => anoise ω j) (fun j => phinoise ω j) i ∂Pr = 0) ∧
    (∀ i j, covariance
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr =
      (abar i * abar j * (Real.cosh (Rφ i j) - 1) + Ra i j * Real.cosh (Rφ i j)) *
        Real.exp (-((Rφ i i + Rφ j j) / 2))) ∧
    (∀ i j, covariance
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr = 0) ∧
    (∀ i j, covariance
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr =
      (abar i * abar j + Ra i j) * Real.sinh (Rφ i j) * Real.exp (-((Rφ i i + Rφ j j) / 2))) := by sorry

end Arxiv0812_1178
