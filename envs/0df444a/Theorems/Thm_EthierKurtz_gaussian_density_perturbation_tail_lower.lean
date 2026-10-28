-- Prove2me | Theorems.Thm_EthierKurtz_gaussian_density_perturbation_tail_lower
-- name    : EthierKurtz.gaussian_density_perturbation_tail_lower
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:01:22.140045+00:00
-- url     : https://prove2.me/theorems/fe6e193f-cd20-4485-abaf-dad8faee1da3
-- title:
--   Lower Cramér tail bound from a relative density estimate
-- statement:
--   Let $c_0\ge0$, $\varepsilon_0>0$ with $c_0\varepsilon_0\le1/16$, $A\ge0$ and $b>0$. Say that $(h,K_0,\varepsilon)$ satisfies (H) if $\varepsilon>0$, $K_0>0$, $h\ge0$ is integrable with $\int h=1$, $K_0\varphi(x)e^{-c_0\varepsilon(1+|x|^3)}\le h(x)\le K_0\varphi(x)e^{c_0\varepsilon(1+|x|^3)}$ for $|x|\le\varepsilon_0/\varepsilon$, and $\int_{|x|>\varepsilon_0/\varepsilon}h\le Ae^{-b/\varepsilon^2}$ ($\varphi$, $\Phi$: standard normal density and distribution function). There are $c_L>0$ and $\varepsilon_1>0$ such that whenever (H) holds, $\varepsilon\le\varepsilon_1$ and $1\le s\le\varepsilon_0/(2\varepsilon)$:
--
--   $$\big(1-\Phi(s)\big)e^{-c_L\varepsilon s^3}\le\int_s^\infty h(x)\,dx.$$
--
--   Role: The lower half of Lemma 2 (a), obtained by integrating the density estimate (b).
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Lemma 2 (a)-(b), p. 38 ((a) is derived from the density estimate (b): 'can be proved similarly'), as required on p. 40 for checking J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. I, Z. Wahrsch. verw. Gebiete 32 (1975) 111-131, https://static.renyi.hu/~major/articles/KMT1.pdf, Lemma 1, formulas (2.6)-(2.7), pp. 118-119

import Mathlib

namespace EthierKurtz

theorem gaussian_density_perturbation_tail_lower :
    ∀ {c0 ε0 A b : ℝ},
      (0 : ℝ) ≤ c0 →
        (0 : ℝ) < ε0 →
          c0 * ε0 ≤ (1 / 16 : ℝ) →
            (0 : ℝ) ≤ A →
              (0 : ℝ) < b →
                ∃ (cL : ℝ) (ε1 : ℝ),
                  (0 : ℝ) < cL ∧
                    (0 : ℝ) < ε1 ∧
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
                            ∀ (s : ℝ),
                              (1 : ℝ) ≤ s →
                                s ≤ ε0 / (2 : ℝ) / ε →
                                  ((1 : ℝ) -
                                        (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) s) *
                                      Real.exp (-(cL * ε * s ^ (3 : ℕ))) ≤
                                    ∫ (x : ℝ) in Set.Ioi s, h x := by sorry

end EthierKurtz
