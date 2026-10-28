-- Prove2me | Theorems.Thm_EthierKurtz_gaussian_tail_variance_perturbation
-- name    : EthierKurtz.gaussian_tail_variance_perturbation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:17:38.428843+00:00
-- url     : https://prove2.me/theorems/637a6a61-8f8d-4161-8c1f-d4839bcd3c67
-- title:
--   Second-order variance perturbation of the Gaussian tail (KMT (4.6))
-- statement:
--   Let $0<m\le s$, $m\le s'$ and $x\ge0$, and let $h(u)=\varphi(u)/(1-\Phi(u))$ be the Gaussian hazard rate. Put $A=h(x/s)\,\frac{x}{2s^3}\,(s'^2-s^2)$ and $B=\big(\frac1{m^5}+\frac{10}{m^6}\big)(x^2+1)(s'^2-s^2)^2$. Then
--
--   $$\big(1-\Phi(x/s)\big)e^{A-B}\le1-\Phi(x/s')\le\big(1-\Phi(x/s)\big)e^{A+B}.$$
--
--   Role: The Taylor expansion of the normal tail in the variance that compares $1-\Phi(x/\sigma_\pi)$ with $1-\Phi(x/\sigma)$ in the averaging step of Lemma 3.
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, proof of Lemma 3, formula (4.6), p. 43

import Mathlib

namespace EthierKurtz

theorem gaussian_tail_variance_perturbation :
    ∀ {m s sp x : ℝ},
      (0 : ℝ) < m →
        m ≤ s →
          m ≤ sp →
            (0 : ℝ) ≤ x →
              (1 : ℝ) - (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / sp) ≤
                  ((1 : ℝ) - (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / s)) *
                    Real.exp
                      ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-((x / s) ^ (2 : ℕ) / (2 : ℝ))) /
                                ((1 : ℝ) -
                                  (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / s)) *
                              x /
                            ((2 : ℝ) * s ^ (3 : ℕ)) *
                          (sp ^ (2 : ℕ) - s ^ (2 : ℕ)) +
                        ((1 : ℝ) / m ^ (5 : ℕ) + (10 : ℝ) / m ^ (6 : ℕ)) * (x ^ (2 : ℕ) + (1 : ℝ)) *
                          (sp ^ (2 : ℕ) - s ^ (2 : ℕ)) ^ (2 : ℕ)) ∧
                ((1 : ℝ) - (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / s)) *
                    Real.exp
                      ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-((x / s) ^ (2 : ℕ) / (2 : ℝ))) /
                                ((1 : ℝ) -
                                  (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / s)) *
                              x /
                            ((2 : ℝ) * s ^ (3 : ℕ)) *
                          (sp ^ (2 : ℕ) - s ^ (2 : ℕ)) -
                        ((1 : ℝ) / m ^ (5 : ℕ) + (10 : ℝ) / m ^ (6 : ℕ)) * (x ^ (2 : ℕ) + (1 : ℝ)) *
                          (sp ^ (2 : ℕ) - s ^ (2 : ℕ)) ^ (2 : ℕ)) ≤
                  (1 : ℝ) - (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / sp) := by sorry

end EthierKurtz
