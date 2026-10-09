-- Prove2me | Theorems.Thm_ExploreFirst_Collective_equation_14
-- name    : ExploreFirst.Collective.equation_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:43.285483+00:00
-- url     : https://prove2.me/theorems/cf0fa862-e45d-4f66-b867-ff6efd68552a
-- title:
--   Equation (14), p. 14 — $x\le(A^\star/K)(1+2T\mathcal K^{\max}+\sqrt{2T\mathcal K^{\max}})$
-- statement:
--   Under the hypotheses and with the notation of the kl display of the proof of Theorem 4 ($\mathcal D$, $\psi$ pairwise symmetric for optimal arms, $\underline\nu$ in $\mathcal D$ with $K\ge1$ arms, a worst arm $\tilde w$ achieving $\mathcal K^{\max}_{\underline\nu}$, the auxiliary problems $\underline{\underline\nu}$ and $\underline{\tilde\nu}$, and $T\ge1$), assume moreover that $\mathcal K^{\max}_{\underline\nu}<+\infty$. Then the fraction
--   $$x=\frac1T\sum_{a^\star\in\mathcal A^\star(\underline\nu)}\mathbb E_{\underline{\underline\nu}}\big[N_{\psi,a^\star}(T)\big]$$
--   satisfies
--   $$x\ \le\ \frac{A^\star_{\underline\nu}}{K}\Big(1+2T\mathcal K^{\max}_{\underline\nu}+\sqrt{2T\mathcal K^{\max}_{\underline\nu}}\Big).\tag{14}$$
--
--   Since the suboptimal arms of $\underline{\underline\nu}$ receive $T(1-x)$ pulls in expectation, (14) is the bound that, through monotonicity, gives Theorem 4.
--
--   **Formalization Note** The finiteness of $\mathcal K^{\max}_{\underline\nu}$ is added so that it can be used as a real number; when it is $+\infty$ the paper's bound is vacuous.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 14, §3.3, proof of Theorem 4, (14)

import Mathlib
import Definitions.Def_ExploreFirst_Collective_Setting

namespace ExploreFirst.Collective

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

/-- Equation (14), p. 14: under the hypotheses of the kl display and `𝒦^max_ν < ∞`,
`x ≤ (A⋆/K)(1 + 2T𝒦^max + √(2T𝒦^max))`. -/
theorem equation_14 {K : ℕ}
    (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K)
    (hπ : ExploreFirst.Relative.IsPairwiseSymmetric 𝒟 π) (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν) (hK : 0 < K)
    (w : Fin K) (hw : w ∈ worstArms ν)
    (hwmin : (ExploreFirst.Asymptotic.optimalArms ν).sup (fun a => InformationTheory.klDiv (ν.P w) (ν.P a)) = kMax ν)
    (νdd : StochasticBandit K)
    (hνdd : ∀ a, νdd.P a = if a ∈ ExploreFirst.Asymptotic.optimalArms ν then ν.P a else ν.P w)
    (νt : StochasticBandit K) (hνt : ∀ a, νt.P a = ν.P w)
    (T : ℕ) (hT : 1 ≤ T)
    (hfin : kMax ν ≠ ⊤) :
    (∑ a ∈ ExploreFirst.Asymptotic.optimalArms ν, ExploreFirst.FundIneq.expPulls νdd π T a) / T
      ≤ ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) / K *
          (1 + 2 * T * (kMax ν).toReal + Real.sqrt (2 * T * (kMax ν).toReal)) := by sorry

end ExploreFirst.Collective
