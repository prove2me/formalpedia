-- Prove2me | Theorems.Thm_FairPricingPerturbation_welfare_sensitivity
-- name    : FairPricingPerturbation.welfare_sensitivity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:13:19.990811+00:00
-- url     : https://prove2.me/theorems/14d52080-14ac-4d25-b9a6-10885c459b41
-- title:
--   Welfare sensitivity of a little fairness: the general perturbation theorem
-- statement:
--   Let $R_i,M_i,S_i:\mathbb R\to\mathbb R$ ($i=0,1$), weights $w_i$ and prices $b_i>0$ satisfy:
--
--   1. $b_i$ maximises $R_i$ on $[0,\infty)$, and near-optimal prices are close to $b_i$: for every $\varepsilon>0$ there is $\delta>0$ with $R_i(p)\ge R_i(b_i)-\delta\Rightarrow|p-b_i|<\varepsilon$;
--   2. $R_i$ and $M_i$ are continuous near $b_i$;
--   3. $R_i(b_i+h)=R_i(b_i)+\tfrac{r_i}{2}h^2+o(h^2)$ with $r_i<0$;
--   4. $M_i'(b_i)=m_i$ with $(m_0,m_1)\ne(0,0)$, and $S_i'(b_i)=\sigma_i$;
--   5. $\Delta=M_0(b_0)-M_1(b_1)\neq0$.
--
--   Put $K=m_0^2/r_0+m_1^2/r_1$, $\mu=-\Delta/K$ and $v^*=(\mu m_0/r_0,\,-\mu m_1/r_1)$. Then, for all small $\alpha\ge0$, the problem
--   $$\max_{p\ge0}\ R_0(p_0)+R_1(p_1)\quad\text{s.t.}\quad|M_0(p_0)-M_1(p_1)|\le(1-\alpha)|\Delta|$$
--   has an optimum, and for every choice $p(\alpha)$ of optima on some $(0,\varepsilon]$,
--   $$\lim_{\alpha\downarrow0}\frac{W(p(\alpha))-W(b)}{\alpha}=w_0\sigma_0v^*_0+w_1\sigma_1v^*_1,\qquad W(p)=\sum_i R_i(p_i)+w_iS_i(p_i).$$
--
--   This is the analytic core of Lemma 1 (Online Appendix A, pp. 31–33): the paper computes $p_i'(0)$ from the KKT conditions assuming the optimal prices are differentiable in $\alpha$; here the conclusion is proved for every selection of optima, with no regularity of $\alpha\mapsto p(\alpha)$ assumed. Here $v^*$ is the minimiser of $\sum_i(-r_i/2)v_i^2$ on the linearised constraint $m_0v_0-m_1v_1=-\Delta$.
--
--   **Formalization Note.** Pure real analysis; no measure theory is involved.
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; Online Appendix A, proof of Lemma 1, pp. 31-33 (Eqs. (4)-(13)), generalised to arbitrary selections of optima.

import Mathlib

open Filter Topology Asymptotics

namespace FairPricingPerturbation

theorem welfare_sensitivity
    (R M S : Fin 2 → ℝ → ℝ) (w b r mm σ : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → R i (b i) - δ ≤ R i p → |p - b i| < ε)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (R i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => R i (b i + h) - R i (b i) - r i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (S i) (σ i) (b i))
    (hgap : M 0 (b 0) ≠ M 1 (b 1)) :
    (∃ ε > 0, ∀ α ∈ Set.Icc (0 : ℝ) ε, ∃ p : Fin 2 → ℝ,
      ((∀ i, 0 ≤ p i) ∧ |M 0 (p 0) - M 1 (p 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      ∀ q : Fin 2 → ℝ,
        ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
        R 0 (q 0) + R 1 (q 1) ≤ R 0 (p 0) + R 1 (p 1)) ∧
    ∀ P : ℝ → Fin 2 → ℝ,
      (∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε,
        ((∀ i, 0 ≤ P α i) ∧
          |M 0 (P α 0) - M 1 (P α 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
          R 0 (q 0) + R 1 (q 1) ≤ R 0 (P α 0) + R 1 (P α 1)) →
      Tendsto (fun α =>
          ((R 0 (P α 0) + R 1 (P α 1) + w 0 * S 0 (P α 0) + w 1 * S 1 (P α 1)) -
            (R 0 (b 0) + R 1 (b 1) + w 0 * S 0 (b 0) + w 1 * S 1 (b 1))) / α)
        (𝓝[>] 0)
        (𝓝 (w 0 * σ 0 * ((-(M 0 (b 0) - M 1 (b 1)) / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
            w 1 * σ 1 * (-((-(M 0 (b 0) - M 1 (b 1)) / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)))) := by
  sorry

end FairPricingPerturbation
