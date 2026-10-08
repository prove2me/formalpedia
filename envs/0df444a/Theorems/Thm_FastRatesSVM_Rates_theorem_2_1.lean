-- Prove2me | Theorems.Thm_FastRatesSVM_Rates_theorem_2_1
-- name    : FastRatesSVM.Rates.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:27.572993+00:00
-- url     : https://prove2.me/theorems/6f77afa3-ddcf-40f6-88dd-1df8c507d20d
-- title:
--   Theorem 2.1 — empirical covering bound for Gaussian RKHS balls
-- statement:
--   Let $d>0$ and let $S\subseteq\mathbb R^d$ be compact with nonempty interior. For $0<p\le2$ and $\delta>0$, there is a constant $c>0$, independent of $\sigma$, sample size, sample and radius, such that for every $\sigma\ge1$, every nonempty sample $T$ in $S\times\{-1,1\}$ and every $\varepsilon>0$,
--   $$
--   \log N(B_{H_\sigma(S)},\varepsilon,L_2(T_X))
--   \le c\,\sigma^{(1-p/2)(1+\delta)d}\varepsilon^{-p}.
--   $$
--
--   The bound controls the Gaussian RKHS hypothesis class as the kernel parameter changes. **Formalization Note** The Lean inequality is $N\le\exp(\text{right side})$, equivalent for the positive finite covering number; this avoids totalized logarithms. The constant may depend on $S,p,\delta,d$.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 5, Theorem 2.1

import Definitions.Def_FastRatesSVM_Rates_Cover

namespace FastRatesSVM.Rates

/-- Theorem 2.1, arXiv:0708.1838v1, p. 5. -/
theorem theorem_2_1 (d : ℕ) (hd : 0 < d) (S : Set (E d))
    (hcompact : IsCompact S) (hinterior : (interior S).Nonempty)
    (p δ : ℝ) (hp : 0 < p ∧ p ≤ 2) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (σ : ℝ), 1 ≤ σ →
      ∀ (n : ℕ), 1 ≤ n →
      ∀ (T : Fin n → E d × ℝ), (∀ i, (T i).1 ∈ S ∧ ((T i).2 = 1 ∨ (T i).2 = -1)) →
      ∀ (ε : ℝ), 0 < ε →
        empiricalCoverNumber (gaussianUnitBall S σ) (fun i => (T i).1) ε ≤
          ENNReal.ofReal
            (Real.exp (c * σ ^ ((1 - p / 2) * (1 + δ) * (d : ℝ)) * ε ^ (-p))) := by sorry

end FastRatesSVM.Rates
