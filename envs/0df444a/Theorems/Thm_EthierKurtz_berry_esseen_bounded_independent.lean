-- Prove2me | Theorems.Thm_EthierKurtz_berry_esseen_bounded_independent
-- name    : EthierKurtz.berry_esseen_bounded_independent
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:15:17.677946+00:00
-- url     : https://prove2.me/theorems/2d9ce187-0c3a-4ee0-8c41-e15fb6ef3787
-- title:
--   Berry–Esseen bound for bounded independent summands
-- statement:
--   Let $\xi_i$ ($i\in\iota$, $\iota$ finite) be independent measurable real random variables on a probability space with $|\xi_i|\le\delta$ everywhere, $E\xi_i=0$ and $\sum_i E\xi_i^2=1$, where $0<\delta\le 1$. Then for every $z\in\mathbb R$
--
--   $$\Big|P\Big(\sum_i\xi_i<z\Big)-\Phi(z)\Big|\le 7\delta,$$
--
--   where $\Phi$ is the standard normal distribution function.
--
--   Role: The normal approximation step behind the Cramér-type estimates (KMT II Lemma B and the i.i.d. Cramér bound); with $|\xi_i|\le\delta$ one has $\sum_i E|\xi_i|^3\le\delta$.
-- source:
--   V. V. Petrov, Sums of Independent Random Variables, Springer 1975, Ch. V, §2, Theorem 3 (Berry–Esseen for non-identically distributed summands); used as in J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Lemma B, pp. 41-42

import Mathlib

namespace EthierKurtz

theorem berry_esseen_bounded_independent :
    ∀ {Ω : Type} [inst : MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
      {ι : Type} [inst_2 : Fintype ι] [DecidableEq ι] (ξ : ι → Ω → ℝ),
      ProbabilityTheory.iIndepFun ξ P →
        (∀ (i : ι), Measurable (ξ i)) →
          ∀ {δ : ℝ},
            (0 : ℝ) < δ →
              (∀ (i : ι) (ω : Ω), |ξ i ω| ≤ δ) →
                (∀ (i : ι), ∫ (ω : Ω), ξ i ω ∂P = (0 : ℝ)) →
                  ∑ i : ι, ∫ (ω : Ω), ξ i ω ^ (2 : ℕ) ∂P = (1 : ℝ) →
                    δ ≤ (1 : ℝ) →
                      ∀ (z : ℝ),
                        |ENNReal.toReal (P {ω : Ω | ∑ i : ι, ξ i ω < z}) -
                              (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) z| ≤
                          (7 : ℝ) * δ := by sorry

end EthierKurtz
