-- Prove2me | Theorems.Thm_ExploreFirst_Collective_uniform_split
-- name    : ExploreFirst.Collective.uniform_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:49.310258+00:00
-- url     : https://prove2.me/theorems/cdcf97eb-9d96-452b-b145-60a8ac962f00
-- title:
--   Proof of Theorem 4, p. 13 — on a problem with identical arms, a pairwise symmetric strategy pulls every arm $T/K$ times in expectation
-- statement:
--   Let $\mathcal D$ be a model of distributions with an expectation and let $\psi$ be a strategy that is pairwise symmetric for optimal arms on $\mathcal D$ (Definition 3). Let $\underline{\tilde\nu}$ be a bandit problem in $\mathcal D$ whose $K$ arms all have the same distribution. Then for all $T\ge1$ and every arm $a$,
--   $$\mathbb E_{\underline{\tilde\nu}}\big[N_{\psi,a}(T)\big]=\frac TK.$$
--
--   In the proof of Theorem 4 this is applied to the problem $\underline{\tilde\nu}$ in which every arm carries the distribution $\nu_{\tilde w}$ of a worst arm; all its arms are optimal, so pairwise symmetry applies to every pair.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 13, §3.3, proof of Theorem 4, last two sentences

import Mathlib
import Definitions.Def_ExploreFirst_Collective_Setting

namespace ExploreFirst.Collective

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

/-- Proof of Theorem 4, p. 13, last lines: if every arm of `ν̰` has the same distribution and
`ψ` is pairwise symmetric for optimal arms on `𝒟`, then `𝔼_ν̰[N_a(T)] = T/K` for every arm `a`. -/
theorem uniform_split {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K)
    (hπ : ExploreFirst.Relative.IsPairwiseSymmetric 𝒟 π) (νt : StochasticBandit K) (hνt : ExploreFirst.Asymptotic.InModel 𝒟 νt)
    (hsame : ∀ a b, νt.P a = νt.P b) (T : ℕ) (hT : 1 ≤ T) (a : Fin K) :
    ExploreFirst.FundIneq.expPulls νt π T a = (T : ℝ) / K := by sorry

end ExploreFirst.Collective
