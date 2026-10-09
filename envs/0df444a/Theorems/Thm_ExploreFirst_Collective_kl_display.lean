-- Prove2me | Theorems.Thm_ExploreFirst_Collective_kl_display
-- name    : ExploreFirst.Collective.kl_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:05:54.637644+00:00
-- url     : https://prove2.me/theorems/00575453-1d21-4cf4-b377-9a601b2c8efb
-- title:
--   Proof of Theorem 4, p. 14 — $T A^\star\mathcal K^{\max}/K\ge\mathrm{kl}(A^\star/K,x)$
-- statement:
--   Let $\mathcal D$ be a model of distributions with an expectation, $\psi$ a strategy pairwise symmetric for optimal arms on $\mathcal D$, and $\underline\nu$ a bandit problem in $\mathcal D$ with $K\ge1$ arms. Let $\tilde w\in\mathcal W(\underline\nu)$ be a worst arm achieving the minimum in the definition of $\mathcal K^{\max}_{\underline\nu}$, i.e. $\max_{a^\star\in\mathcal A^\star(\underline\nu)}\mathrm{KL}(\nu_{\tilde w},\nu_{a^\star})=\mathcal K^{\max}_{\underline\nu}$. Consider the two auxiliary problems
--   $$\underline{\underline\nu}_a=\begin{cases}\nu_a&a\in\mathcal A^\star(\underline\nu)\\ \nu_{\tilde w}&a\notin\mathcal A^\star(\underline\nu)\end{cases},\qquad \underline{\tilde\nu}_a=\nu_{\tilde w}\ \text{ for all }a.$$
--   For $T\ge1$ put
--   $$x=\frac1T\sum_{a^\star\in\mathcal A^\star(\underline\nu)}\mathbb E_{\underline{\underline\nu}}\big[N_{\psi,a^\star}(T)\big].$$
--   Then
--   $$\frac{T A^\star_{\underline\nu}\,\mathcal K^{\max}_{\underline\nu}}{K}\ \ge\ \mathrm{kl}\Big(\frac{A^\star_{\underline\nu}}K,\ x\Big).$$
--
--   This is the information-theoretic step of the proof of Theorem 4: the fundamental inequality (6) between $\underline{\tilde\nu}$ and $\underline{\underline\nu}$, with $Z=\sum_{a^\star}N_{\psi,a^\star}(T)/T$, combined with $\mathbb E_{\underline{\tilde\nu}}[N_{\psi,a}(T)]=T/K$.
--
--   **Formalization Note** Both sides are in $[0,+\infty]$; $\mathcal K^{\max}$ may be $+\infty$, in which case the inequality is trivial. The auxiliary problems are not constructed but quantified over with their defining properties.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 14, §3.3, proof of Theorem 4, display after "which yields the inequality"

import Mathlib
import Definitions.Def_ExploreFirst_Collective_Setting

namespace ExploreFirst.Collective

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

/-- Proof of Theorem 4, p. 14: with `w` a worst arm attaining the minimum in `𝒦^max_ν`, `ν̳` and
`ν̰` the two auxiliary problems, and `x = (1/T) ∑_{a⋆ ∈ 𝒜⋆(ν)} 𝔼_ν̳[N_{a⋆}(T)]`,
`T A⋆ 𝒦^max / K ≥ kl(A⋆/K, x)`. -/
theorem kl_display {K : ℕ}
    (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K)
    (hπ : ExploreFirst.Relative.IsPairwiseSymmetric 𝒟 π) (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν) (hK : 0 < K)
    (w : Fin K) (hw : w ∈ worstArms ν)
    (hwmin : (ExploreFirst.Asymptotic.optimalArms ν).sup (fun a => InformationTheory.klDiv (ν.P w) (ν.P a)) = kMax ν)
    (νdd : StochasticBandit K)
    (hνdd : ∀ a, νdd.P a = if a ∈ ExploreFirst.Asymptotic.optimalArms ν then ν.P a else ν.P w)
    (νt : StochasticBandit K) (hνt : ∀ a, νt.P a = ν.P w)
    (T : ℕ) (hT : 1 ≤ T) :
    ExploreFirst.FundIneq.klBer (((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) / K) ((∑ a ∈ ExploreFirst.Asymptotic.optimalArms ν, ExploreFirst.FundIneq.expPulls νdd π T a) / T)
      ≤ ENNReal.ofReal ((T : ℝ) * (ExploreFirst.Asymptotic.optimalArms ν).card / K) * kMax ν := by sorry

end ExploreFirst.Collective
