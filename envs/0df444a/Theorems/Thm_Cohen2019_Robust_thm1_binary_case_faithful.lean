-- Prove2me | Theorems.Thm_Cohen2019_Robust_thm1_binary_case_faithful
-- name    : Cohen2019.Robust.thm1_binary_case_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T01:33:52.617145+00:00
-- url     : https://prove2.me/theorems/5232569c-0451-43f4-81fb-d826224e6485
-- title:
--   Theorem 1 (binary case): radius $\sigma\Phi^{-1}(\underline{p_A})$ with two classes
-- statement:
--   Let $\mathcal Y=\{c_A,c_B\}$ have two classes, let $f:\mathbb R^d\to\mathcal Y$ be any deterministic or random function, let $\sigma>0$, $\varepsilon\sim\mathcal N(0,\sigma^2I)$, and let $g(x)=\arg\max_{c}\mathbb P(f(x+\varepsilon)=c)$. Suppose $\underline{p_A}\in(\tfrac12,1]$ satisfies $\mathbb P(f(x+\varepsilon)=c_A)\ge\underline{p_A}$. Then
--
--   $$g(x+\delta)=c_A\quad\text{for all }\|\delta\|_2<\sigma\,\Phi^{-1}(\underline{p_A}).$$
--
--   This is the binary case of Theorem 1 of Cohen, Rosenfeld and Kolter, stated on p. 4 before the proof sketch; it is Theorem 1 with $\overline{p_B}=1-\underline{p_A}$, for which $R=\frac\sigma2(\Phi^{-1}(\underline{p_A})-\Phi^{-1}(1-\underline{p_A}))=\sigma\Phi^{-1}(\underline{p_A})$.
--
--   **Formalization Note** A random classifier is a map to probability mass functions on $\mathcal Y$ with measurable class probabilities. "$g(x+\delta)=c_A$" means $c_A$ is the strict unique maximizer. The radius is an extended real, $+\infty$ when $\underline{p_A}=1$.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, ICML 2019, arXiv:1902.02918v2, p. 4, Theorem 1 (binary case)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Model

open MeasureTheory ProbabilityTheory Cohen2019.Robust

theorem Cohen2019.Robust.thm1_binary_case_faithful {d : ℕ} {Y : Type*}
    (f : EuclideanSpace ℝ (Fin d) → PMF Y) (hf : ∀ c : Y, Measurable fun z => f z c)
    (σ : ℝ) (hσ : 0 < σ) (x : EuclideanSpace ℝ (Fin d)) (cA cB : Y) (hAB : cA ≠ cB)
    (hY : ∀ c : Y, c = cA ∨ c = cB) (pA : ℝ) (hpA0 : 1 / 2 < pA) (hpA1 : pA ≤ 1)
    (hA : pA ≤ classProb f σ x cA) :
    ∀ δ : EuclideanSpace ℝ (Fin d), ((‖δ‖ : ℝ) : EReal) < ((σ : ℝ) : EReal) * PhiInv pA →
      IsSmoothedPrediction f σ (x + δ) cA := by sorry
