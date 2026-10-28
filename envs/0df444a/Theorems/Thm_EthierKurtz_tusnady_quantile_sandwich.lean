-- Prove2me | Theorems.Thm_EthierKurtz_tusnady_quantile_sandwich
-- name    : EthierKurtz.tusnady_quantile_sandwich
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:12:52.249178+00:00
-- url     : https://prove2.me/theorems/0982410c-e0fa-4574-b6d6-6b48885fac30
-- title:
--   Tusnády-type quantile sandwich from Cramér tail bounds
-- statement:
--   Let $c_R,\varepsilon_R,c_L,\varepsilon_L,K>0$. There are $c,\varepsilon>0$ and $m_0\ge1$ such that for every $m\ge m_0$ and every probability law $L$ on $\mathbb R$ with distribution function $F_L$ satisfying
--
--   $$\big(1-\Phi(\tfrac{y}{\sqrt m})\big)e^{-c_R y^3/m^2}\le L((y,\infty))\le\big(1-\Phi(\tfrac{y}{\sqrt m})\big)e^{c_R y^3/m^2}\quad(\sqrt m\le y\le\varepsilon_R m),$$
--
--   the same bounds for $L((-\infty,-y))$ with $c_L$ for $\sqrt m\le y\le\varepsilon_L m$, and $|F_L(\sqrt m\,z)-\Phi(z)|\le K/\sqrt m$ for $|z|\le3$, we have for all $|y|\le\varepsilon m$
--
--   $$F_L\Big(y-c\big(1+\tfrac{y^2}{m}\big)\Big)\le\Phi\big(\tfrac{y}{\sqrt m}\big)\le F_L\Big(y+c\big(1+\tfrac{y^2}{m}\big)\Big).$$
--
--   Role: The deterministic step that turns Cramér-type tail estimates into the quantile coupling bound $|S-T|\le C(1+S^2/m)$, used at the root and at every node of the dyadic construction.
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. I, Z. Wahrsch. verw. Gebiete 32 (1975) 111-131, https://static.renyi.hu/~major/articles/KMT1.pdf, Lemma 1, proof of formulas (2.6)-(2.7), pp. 118-119; used in J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, pp. 47-49

import Mathlib

namespace EthierKurtz

theorem tusnady_quantile_sandwich :
    ∀ (cR εR cL εL K : ℝ),
      (0 : ℝ) < cR →
        (0 : ℝ) < εR →
          (0 : ℝ) < cL →
            (0 : ℝ) < εL →
              (0 : ℝ) < K →
                ∃ (c : ℝ) (ε : ℝ) (m₀ : ℕ),
                  (0 : ℝ) < c ∧
                    (0 : ℝ) < ε ∧
                      (1 : ℕ) ≤ m₀ ∧
                        ∀ (m : ℕ),
                          m₀ ≤ m →
                            ∀ (L : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure L],
                              (∀ (y : ℝ),
                                  √↑m ≤ y →
                                    y ≤ εR * ↑m →
                                      MeasureTheory.Measure.real L (Set.Ioi y) ≤
                                          ((1 : ℝ) -
                                              (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                (y / √↑m)) *
                                            Real.exp (cR * (y ^ (3 : ℕ) / ↑m ^ (2 : ℕ))) ∧
                                        ((1 : ℝ) -
                                              (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                (y / √↑m)) *
                                            Real.exp (-(cR * (y ^ (3 : ℕ) / ↑m ^ (2 : ℕ)))) ≤
                                          MeasureTheory.Measure.real L (Set.Ioi y)) →
                                (∀ (y : ℝ),
                                    √↑m ≤ y →
                                      y ≤ εL * ↑m →
                                        MeasureTheory.Measure.real L (Set.Iio (-y)) ≤
                                            ((1 : ℝ) -
                                                (ProbabilityTheory.cdf
                                                      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                  (y / √↑m)) *
                                              Real.exp (cL * (y ^ (3 : ℕ) / ↑m ^ (2 : ℕ))) ∧
                                          ((1 : ℝ) -
                                                (ProbabilityTheory.cdf
                                                      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                  (y / √↑m)) *
                                              Real.exp (-(cL * (y ^ (3 : ℕ) / ↑m ^ (2 : ℕ)))) ≤
                                            MeasureTheory.Measure.real L (Set.Iio (-y))) →
                                  (∀ (z : ℝ),
                                      |z| ≤ (3 : ℝ) →
                                        (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) z -
                                              K / √↑m ≤
                                            (ProbabilityTheory.cdf L) (√↑m * z) ∧
                                          (ProbabilityTheory.cdf L) (√↑m * z) ≤
                                            (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                z +
                                              K / √↑m) →
                                    ∀ (y : ℝ),
                                      |y| ≤ ε * ↑m →
                                        (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                              (y / √↑m) ≤
                                            (ProbabilityTheory.cdf L) (y + c * ((1 : ℝ) + y ^ (2 : ℕ) / ↑m)) ∧
                                          (ProbabilityTheory.cdf L) (y - c * ((1 : ℝ) + y ^ (2 : ℕ) / ↑m)) ≤
                                            (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                              (y / √↑m) := by sorry

end EthierKurtz
