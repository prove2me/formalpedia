-- Prove2me | Theorems.Thm_EthierKurtz_gaussian_density_perturbation_normalization
-- name    : EthierKurtz.gaussian_density_perturbation_normalization
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:58:27.463917+00:00
-- url     : https://prove2.me/theorems/03028575-7736-45bf-a87e-051fcf81aad5
-- title:
--   Normalisation of a density close to the Gaussian in Cramér's relative sense
-- statement:
--   Let $c_0\ge0$, $\varepsilon_0>0$ with $c_0\varepsilon_0\le1/16$, $A\ge0$ and $b>0$. Say that $(h,K_0,\varepsilon)$ satisfies (H) if $\varepsilon>0$, $K_0>0$, $h\ge0$ is integrable with $\int h=1$, $K_0\varphi(x)e^{-c_0\varepsilon(1+|x|^3)}\le h(x)\le K_0\varphi(x)e^{c_0\varepsilon(1+|x|^3)}$ for $|x|\le\varepsilon_0/\varepsilon$, and $\int_{|x|>\varepsilon_0/\varepsilon}h\le Ae^{-b/\varepsilon^2}$ ($\varphi$, $\Phi$: standard normal density and distribution function). There are $C_3>0$ and $0<\varepsilon_1\le1$ with $\varepsilon_1c_0\le1$ such that whenever (H) holds and $\varepsilon\le\varepsilon_1$:
--
--   $$|K_0-1|\le C_3\varepsilon,\qquad K_0\le2,\qquad\int|h(x)-\varphi(x)|\,dx\le C_3\varepsilon.$$
--
--   Role: The normalisation step when the tail estimate (a) of Lemma 2 is derived from the density estimate (b).
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Lemma 2 (a)-(b), p. 38 ((a) is derived from the density estimate (b): 'can be proved similarly'), as required on p. 40 for checking J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. I, Z. Wahrsch. verw. Gebiete 32 (1975) 111-131, https://static.renyi.hu/~major/articles/KMT1.pdf, Lemma 1, formulas (2.6)-(2.7), pp. 118-119

import Mathlib

namespace EthierKurtz

theorem gaussian_density_perturbation_normalization :
    ∀ {c0 ε0 A b : ℝ},
      (0 : ℝ) ≤ c0 →
        (0 : ℝ) < ε0 →
          c0 * ε0 ≤ (1 / 16 : ℝ) →
            (0 : ℝ) ≤ A →
              (0 : ℝ) < b →
                ∃ (C3 : ℝ) (ε1 : ℝ),
                  (0 : ℝ) < C3 ∧
                    (0 : ℝ) < ε1 ∧
                      ε1 ≤ (1 : ℝ) ∧
                        ε1 * c0 ≤ (1 : ℝ) ∧
                          ∀ (h : ℝ → ℝ) (K0 ε : ℝ),
                            (0 : ℝ) < ε ∧
                                (0 : ℝ) < K0 ∧
                                  (∀ (x : ℝ), (0 : ℝ) ≤ h x) ∧
                                    MeasureTheory.Integrable h MeasureTheory.MeasureSpace.volume ∧
                                      ∫ (x : ℝ), h x = (1 : ℝ) ∧
                                        (∀ (x : ℝ),
                                            |x| ≤ ε0 / ε →
                                              h x ≤
                                                K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                                  Real.exp (c0 * ε * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ∧
                                          (∀ (x : ℝ),
                                              |x| ≤ ε0 / ε →
                                                K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                                    Real.exp (-(c0 * ε * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ≤
                                                  h x) ∧
                                            ∫ (x : ℝ) in (Set.Icc (-(ε0 / ε)) (ε0 / ε))ᶜ, h x ≤
                                              A * Real.exp (-(b / ε ^ (2 : ℕ))) →
                              ε ≤ ε1 →
                                |K0 - (1 : ℝ)| ≤ C3 * ε ∧
                                  K0 ≤ (2 : ℝ) ∧
                                    ∫ (x : ℝ), |h x - (√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))| ≤
                                      C3 * ε := by sorry

end EthierKurtz
