-- Prove2me | Theorems.Thm_ExploreFirst_Asymptotic_equation_10
-- name    : ExploreFirst.Asymptotic.equation_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:54.256571+00:00
-- url     : https://prove2.me/theorems/078bfe75-64e1-4816-9618-2146171df13f
-- title:
--   Equation (10), p. 9 — one-arm change of measure
-- statement:
--   Consider two $K$-armed bandit problems $\underline\nu$ and $\underline\nu'$ that have identical laws for all arms except possibly $a$. Let $\psi$ be any strategy and $T\ge1$. Write $m=\mathbb E_{\underline\nu}N_{\psi,a}(T)$ and $m'=\mathbb E_{\underline\nu'}N_{\psi,a}(T)$. Then
--
--   $$
--   m\,\mathrm{KL}(\nu_a,\nu'_a)
--   \ge \mathrm{kl}(m/T,m'/T)
--   \ge \max\!\left\{0,\left(1-\frac mT\right)\ln\frac{T}{T-m'}-\ln2\right\}.
--   $$
--
--   This specializes the paper's fundamental inequality (6) to the draw fraction of one arm, then applies the entropy estimate (11).
--
--   **Formalization Note** The comparison uses extended nonnegative reals for KL. When $m'=T$ and $m<T$, the last lower bound is explicitly $+\infty$, matching the Bernoulli KL boundary value.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 9, proof of Theorem 1, (10); p. 6, (6)

import Mathlib
import Definitions.Def_ExploreFirst_Asymptotic_Setting

namespace ExploreFirst.Asymptotic

theorem equation_10 {K : ℕ} (ν ν' : BanditAlgorithm.StochasticBandit K)
    (π : BanditAlgorithm.BanditPolicy K) (a : Fin K) (T : ℕ)
    (hT : 1 ≤ T) (hother : ∀ k, k ≠ a → ν'.P k = ν.P k) :
    ExploreFirst.FundIneq.klBer (ExploreFirst.FundIneq.expPulls ν π T a / (T : ℝ)) (ExploreFirst.FundIneq.expPulls ν' π T a / (T : ℝ)) ≤
      ENNReal.ofReal (ExploreFirst.FundIneq.expPulls ν π T a) * InformationTheory.klDiv (ν.P a) (ν'.P a) ∧
    (if ExploreFirst.FundIneq.expPulls ν' π T a / (T : ℝ) = 1 ∧
        ExploreFirst.FundIneq.expPulls ν π T a / (T : ℝ) < 1 then (⊤ : ENNReal)
      else ENNReal.ofReal
        ((1 - ExploreFirst.FundIneq.expPulls ν π T a / (T : ℝ)) *
          Real.log ((T : ℝ) / ((T : ℝ) - ExploreFirst.FundIneq.expPulls ν' π T a)) - Real.log 2)) ≤
      ExploreFirst.FundIneq.klBer (ExploreFirst.FundIneq.expPulls ν π T a / (T : ℝ)) (ExploreFirst.FundIneq.expPulls ν' π T a / (T : ℝ)) := by sorry

end ExploreFirst.Asymptotic
