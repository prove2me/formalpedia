-- Prove2me | Theorems.Thm_EthierKurtz_cramer_iid_bounded_tail_ratio
-- name    : EthierKurtz.cramer_iid_bounded_tail_ratio
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:53:05.204055+00:00
-- url     : https://prove2.me/theorems/cac0448c-2501-4d9c-9e3a-049bb11b1105
-- title:
--   Cramér's large deviation bound for bounded i.i.d. sums
-- statement:
--   Let $F$ be a probability law on $\mathbb R$ with $|x|\le K$ $F$-a.s. ($K>0$), $\int x\,dF=0$ and $\int x^2\,dF=1$. Then there are $c,\varepsilon>0$ such that for every finite index type $\iota$ with $n=|\iota|\ge1$ and every $\sqrt n\le y\le\varepsilon n$, with $X_i$ i.i.d. $F$,
--
--   $$\Big(1-\Phi\big(\tfrac{y}{\sqrt n}\big)\Big)e^{-c\,y^3/n^2}\le P\Big(\sum_{i\in\iota}X_i>y\Big)\le\Big(1-\Phi\big(\tfrac{y}{\sqrt n}\big)\Big)e^{c\,y^3/n^2}.$$
--
--   Role: The tail estimate that feeds the quantile-transform bound for the root of the dyadic scheme (formula (2.6) of Lemma 1 of Part I, used on p. 47 of Part II).
-- source:
--   H. Cramér's large deviation theorem, V. V. Petrov, Sums of Independent Random Variables, Springer 1975, Ch. VIII, §2, Theorems 1-2; used in J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. I, Z. Wahrsch. verw. Gebiete 32 (1975) 111-131, https://static.renyi.hu/~major/articles/KMT1.pdf, Lemma 1, formula (2.6), p. 118, and in J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, p. 47

import Mathlib

namespace EthierKurtz

theorem cramer_iid_bounded_tail_ratio :
    ∀ {F : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure F] {K : ℝ},
      (0 : ℝ) < K →
        (∀ᵐ (x : ℝ) ∂F, |x| ≤ K) →
          ∫ (x : ℝ), x ∂F = (0 : ℝ) →
            ∫ (x : ℝ), x ^ (2 : ℕ) ∂F = (1 : ℝ) →
              ∃ (c : ℝ) (ε : ℝ),
                (0 : ℝ) < c ∧
                  (0 : ℝ) < ε ∧
                    ∀ (ι : Type) [inst : Fintype ι] [DecidableEq ι],
                      (1 : ℕ) ≤ Fintype.card ι →
                        ∀ (y : ℝ),
                          √↑(Fintype.card ι) ≤ y →
                            y ≤ ε * ↑(Fintype.card ι) →
                              MeasureTheory.Measure.real (MeasureTheory.Measure.pi fun (x : ι) => F)
                                    {x : ι → ℝ | y < ∑ i : ι, x i} ≤
                                  ((1 : ℝ) -
                                      (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                        (y / √↑(Fintype.card ι))) *
                                    Real.exp (c * (y ^ (3 : ℕ) / ↑(Fintype.card ι) ^ (2 : ℕ))) ∧
                                ((1 : ℝ) -
                                      (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                        (y / √↑(Fintype.card ι))) *
                                    Real.exp (-(c * (y ^ (3 : ℕ) / ↑(Fintype.card ι) ^ (2 : ℕ)))) ≤
                                  MeasureTheory.Measure.real (MeasureTheory.Measure.pi fun (x : ι) => F)
                                    {x : ι → ℝ | y < ∑ i : ι, x i} := by sorry

end EthierKurtz
