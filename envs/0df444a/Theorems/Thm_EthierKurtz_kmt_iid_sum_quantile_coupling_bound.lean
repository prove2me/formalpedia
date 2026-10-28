-- Prove2me | Theorems.Thm_EthierKurtz_kmt_iid_sum_quantile_coupling_bound
-- name    : EthierKurtz.kmt_iid_sum_quantile_coupling_bound
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:42:17.618077+00:00
-- url     : https://prove2.me/theorems/5a51d94b-94e6-4482-b185-26ae6e8add61
-- title:
--   Quantile coupling of a bounded i.i.d. sum with a normal variable
-- statement:
--   Let $F$ be a probability law on $\mathbb R$ with $|x|\le K$ $F$-a.s. ($K>0$), $\int x\,dF=0$ and $\int x^2\,dF=1$. Then there are $C>0$ and $m_0\ge1$ such that for every finite index type $\iota$ with $n=|\iota|\ge m_0$, writing $G_n$ for the distribution function of $\sum_{i\in\iota}X_i$ ($X_i$ i.i.d. $F$) and $G_n^{-1}(t)=\inf\{x: t\le G_n(x)\}$, every $w\in\mathbb R$ satisfies
--
--   $$\Big|G_n^{-1}\big(\Phi(w/\sqrt n)\big)-w\Big|\le C\Big(1+\frac{w^2}{n}\Big).$$
--
--   Role: The root step of the dyadic construction in the proof of Theorem 1B: the normal variable $T_N$ with $|S_N-T_N|\le C_1S_N^2/N+C_2$.
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Section 4, proof of Theorem 1B, p. 47 (via J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. I, Z. Wahrsch. verw. Gebiete 32 (1975) 111-131, https://static.renyi.hu/~major/articles/KMT1.pdf, Lemma 1, formula (2.6), p. 118)

import Mathlib

namespace EthierKurtz

theorem kmt_iid_sum_quantile_coupling_bound :
    ∀ {F : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure F] {K : ℝ},
      (0 : ℝ) < K →
        (∀ᵐ (x : ℝ) ∂F, |x| ≤ K) →
          ∫ (x : ℝ), x ∂F = (0 : ℝ) →
            ∫ (x : ℝ), x ^ (2 : ℕ) ∂F = (1 : ℝ) →
              ∃ (C : ℝ) (m₀ : ℕ),
                (0 : ℝ) < C ∧
                  (1 : ℕ) ≤ m₀ ∧
                    ∀ (ι : Type) [inst : Fintype ι] [DecidableEq ι],
                      m₀ ≤ Fintype.card ι →
                        ∀ (w : ℝ),
                          |InfSet.sInf
                                  {x : ℝ |
                                    (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                        (w / √↑(Fintype.card ι)) ≤
                                      (ProbabilityTheory.cdf
                                            (MeasureTheory.Measure.map (fun (x : ι → ℝ) => ∑ i : ι, x i)
                                              (MeasureTheory.Measure.pi fun (x : ι) => F)))
                                        x} -
                                w| ≤
                            C * ((1 : ℝ) + w ^ (2 : ℕ) / ↑(Fintype.card ι)) := by sorry

end EthierKurtz
