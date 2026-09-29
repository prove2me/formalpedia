-- Prove2me | Theorems.Thm_BanditAlgorithm_weissman_l1_deviation
-- name    : BanditAlgorithm.weissman_l1_deviation
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T03:58:19.494833+00:00
-- url     : https://prove2.me/theorems/c4a181b3-6f64-4da6-a10a-07996e06e1d1
-- title:
--   Weissman's $\ell_1$ deviation bound for an empirical distribution
-- statement:
--   Let $X_1, \dots, X_m$ be independent random variables with values in a finite set $\iota$ and common law $p$, and let
--
--   $$\hat p_m(a) = \frac{1}{m}\sum_{i=1}^m \mathbb{1}\{X_i = a\}$$
--
--   be their empirical distribution. Then for every $\varepsilon \ge 0$,
--
--   $$\mathbb{P}\big(\|\hat p_m - p\|_1 \ge \varepsilon\big) \;\le\; 2^{|\iota|}\,\exp\!\left(-\frac{m\varepsilon^2}{2}\right).$$
--
--   This is the fixed-sample-size categorical concentration inequality of Weissman, Ordentlich, Seroussi, Verdú and Weinberger, and it is the probabilistic content of Lemma 38.8 in Lattimore and Szepesvári: it is what makes the $\ell^1$ confidence sets
--
--   $$\mathcal{C}_t(s,a) = \Big\{P : \|P - \hat P_{t-1,a}(s)\|_1 \le \sqrt{\tfrac{S L_{t-1}(s,a)}{1 \vee T_{t-1}(s,a)}}\Big\}$$
--
--   of Eq. (38.13) valid, and it explains both the shape of the confidence width and the appearance of $S$ inside it: setting the right-hand side equal to $\delta'$ gives $\varepsilon = \sqrt{2(|\iota|\log 2 + \log(1/\delta'))/m}$, of the stated order $\sqrt{S/m}$ up to the logarithmic term.
--
--   The proof has two halves. The deterministic half is the variational identity $\|\hat p - p\|_1 = 2\max_{A \subseteq \iota}(\hat p(A) - p(A))$, which shows that an $\ell^1$ deviation of $\varepsilon$ forces one of the $2^{|\iota|}$ events $A$ to have empirical probability exceeding its true probability by $\varepsilon/2$; a union bound over the subsets produces the factor $2^{|\iota|}$. The probabilistic half is Hoeffding's inequality applied to each fixed $A$: the indicators $\mathbb{1}\{X_i \in A\}$ are independent and take values in $[0,1]$, hence are sub-Gaussian with variance proxy $1/4$, and
--
--   $$\mathbb{P}\Big(\sum_{i=1}^m \big(\mathbb{1}\{X_i \in A\} - p(A)\big) \ge \tfrac{m\varepsilon}{2}\Big) \le \exp\!\left(-\frac{(m\varepsilon/2)^2}{2 \cdot m/4}\right) = \exp\!\left(-\frac{m\varepsilon^2}{2}\right).$$
--
--   The hypothesis $m > 0$ only rules out the empty sample, for which the empirical distribution is not defined.
-- source:
--   Weissman, Ordentlich, Seroussi, Verdu & Weinberger, Inequalities for the L1 deviation of the empirical distribution, HP Labs Tech. Report HPL-2003-97 (2003); used as Lemma 38.8 / Exercise 38.21 of Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), for the confidence sets Eq. (38.13) of UCRL2; Jaksch, Ortner & Auer, JMLR 11 (2010), Appendix C.1.

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem BanditAlgorithm.weissman_l1_deviation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] {m : ℕ} (hm : 0 < m)
    (X : Fin m → Ω → ι) (p : ι → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ)
    (hlaw : ∀ (i : Fin m) (a : ι), μ.real {ω | X i ω = a} = p a)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ a, |(∑ i : Fin m, if X i ω = a then (1 : ℝ) else 0) / m - p a|}
      ≤ 2 ^ Fintype.card ι * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  sorry
