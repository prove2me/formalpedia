-- Prove2me | Theorems.Thm_EthierKurtz_gaussian_density_perturbation_quantile_sandwich
-- name    : EthierKurtz.gaussian_density_perturbation_quantile_sandwich
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:40:10.045107+00:00
-- url     : https://prove2.me/theorems/202a70f8-2bcf-4ad7-bfbf-6399d21b0a82
-- title:
--   Tusnády quantile sandwich for densities satisfying Cramér-type estimates
-- statement:
--   Let $c_0\ge0$, $\varepsilon_0>0$ with $c_0\varepsilon_0\le1/16$, $A\ge0$ and $b>0$. Say that $(h,K_0,\varepsilon)$ satisfies (H) if $\varepsilon>0$, $K_0>0$, $h\ge0$ is integrable with $\int h=1$, $K_0\varphi(x)e^{-c_0\varepsilon(1+|x|^3)}\le h(x)\le K_0\varphi(x)e^{c_0\varepsilon(1+|x|^3)}$ for $|x|\le\varepsilon_0/\varepsilon$, and $\int_{|x|>\varepsilon_0/\varepsilon}h\le Ae^{-b/\varepsilon^2}$ ($\varphi$, $\Phi$: standard normal density and distribution function). There are $c>0$, $\varepsilon_t>0$ and $m_0\ge1$ such that for every $m\ge m_0$ and every $(h,K_0)$ with (H) at $\varepsilon=1/\sqrt m$, writing $F$ for the distribution function of $\sqrt m\,Y$ where $Y$ has density $h$, every $|y|\le\varepsilon_tm$ satisfies
--
--   $$F\Big(y-c\big(1+\tfrac{y^2}m\big)\Big)\le\Phi\big(\tfrac y{\sqrt m}\big)\le F\Big(y+c\big(1+\tfrac{y^2}m\big)\Big).$$
--
--   Role: The quantile-transform step of the proof of Theorem 1A ('one has only to check Lemma 1 of part I'), applied to the densities estimated in Lemma 2.
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Lemma 2 (a)-(b), p. 38 ((a) is derived from the density estimate (b): 'can be proved similarly'), as required on p. 40 for checking J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. I, Z. Wahrsch. verw. Gebiete 32 (1975) 111-131, https://static.renyi.hu/~major/articles/KMT1.pdf, Lemma 1, formulas (2.6)-(2.7), pp. 118-119

import Mathlib

namespace EthierKurtz

theorem gaussian_density_perturbation_quantile_sandwich :
    ∀ {c0 ε0 A b : ℝ},
      (0 : ℝ) ≤ c0 →
        (0 : ℝ) < ε0 →
          c0 * ε0 ≤ (1 / 16 : ℝ) →
            (0 : ℝ) ≤ A →
              (0 : ℝ) < b →
                ∃ (c : ℝ) (εt : ℝ) (m₀ : ℕ),
                  (0 : ℝ) < c ∧
                    (0 : ℝ) < εt ∧
                      (1 : ℕ) ≤ m₀ ∧
                        ∀ (m : ℕ),
                          m₀ ≤ m →
                            ∀ (h : ℝ → ℝ) (K0 : ℝ),
                              (0 : ℝ) < (1 : ℝ) / √↑m ∧
                                  (0 : ℝ) < K0 ∧
                                    (∀ (x : ℝ), (0 : ℝ) ≤ h x) ∧
                                      MeasureTheory.Integrable h MeasureTheory.MeasureSpace.volume ∧
                                        ∫ (x : ℝ), h x = (1 : ℝ) ∧
                                          (∀ (x : ℝ),
                                              |x| ≤ ε0 / ((1 : ℝ) / √↑m) →
                                                h x ≤
                                                  K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                                    Real.exp (c0 * ((1 : ℝ) / √↑m) * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ∧
                                            (∀ (x : ℝ),
                                                |x| ≤ ε0 / ((1 : ℝ) / √↑m) →
                                                  K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                                      Real.exp (-(c0 * ((1 : ℝ) / √↑m) * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ≤
                                                    h x) ∧
                                              ∫ (x : ℝ) in (Set.Icc (-(ε0 / ((1 : ℝ) / √↑m))) (ε0 / ((1 : ℝ) / √↑m)))ᶜ,
                                                  h x ≤
                                                A * Real.exp (-(b / ((1 : ℝ) / √↑m) ^ (2 : ℕ))) →
                                ∀ (y : ℝ),
                                  |y| ≤ εt * ↑m →
                                    (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                          (y / √↑m) ≤
                                        (ProbabilityTheory.cdf
                                              (MeasureTheory.Measure.map (fun (x : ℝ) => √↑m * x)
                                                (MeasureTheory.Measure.withDensity MeasureTheory.MeasureSpace.volume
                                                  fun (x : ℝ) => ENNReal.ofReal (h x))))
                                          (y + c * ((1 : ℝ) + y ^ (2 : ℕ) / ↑m)) ∧
                                      (ProbabilityTheory.cdf
                                              (MeasureTheory.Measure.map (fun (x : ℝ) => √↑m * x)
                                                (MeasureTheory.Measure.withDensity MeasureTheory.MeasureSpace.volume
                                                  fun (x : ℝ) => ENNReal.ofReal (h x))))
                                          (y - c * ((1 : ℝ) + y ^ (2 : ℕ) / ↑m)) ≤
                                        (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                          (y / √↑m) := by sorry

end EthierKurtz
