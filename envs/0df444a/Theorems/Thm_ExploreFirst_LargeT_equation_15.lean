-- Prove2me | Theorems.Thm_ExploreFirst_LargeT_equation_15
-- name    : ExploreFirst.LargeT.equation_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:50.768392+00:00
-- url     : https://prove2.me/theorems/567416d6-6929-46d0-8357-0581d453993f
-- title:
--   (15), p. 16 — one-alternative lower bound using optimal-arm pulls
-- statement:
--   Let $\psi$ be a uniformly super-fast convergent strategy on a model $\mathcal D$ with constant $C_{\psi,\mathcal D}$. Let $\underline\nu$ be a bandit problem in that model and let $a$ be a suboptimal arm. Form a second problem $\underline\nu'$ by changing only arm $a$ to a law in $\mathcal D$ whose mean exceeds the original optimal mean. For $T\ge2$, let $Z$ be the fraction of the first $T$ pulls allocated to arms optimal under $\underline\nu$. If the divergence between the two laws of arm $a$ is finite, then
--   $$
--   \mathbb E_{\underline\nu}[N_{\psi,a}(T)]\ge
--   \frac{\mathbb E_{\underline\nu}[Z]\ln(1/\mathbb E_{\underline\nu'}[Z])-\ln 2}
--   {\mathrm{KL}(\nu_a,\nu'_a)}.
--   $$
--   This is the change-of-measure bound used to derive the large-horizon estimate.
--
--   **Formalization Note** Every law in $\mathcal D$ is a probability law with an integrable reward. The alternative's unchanged arm laws agree exactly. The finite-KL condition permits real division. With finite KL, if $\mathbb E_{\underline\nu'}[Z]=0$, then $\mathbb E_{\underline\nu}[Z]=0$ as well; the product involving the logarithm uses the standard zero convention.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 16, (15)

import Mathlib
import Definitions.Def_ExploreFirst_LargeT_Setting

namespace ExploreFirst.LargeT

open MeasureTheory BanditAlgorithm

/-- Equation (15): one-arm change of measure for the fraction of optimal-arm pulls. -/
theorem equation_15 {K : ℕ} (𝒟 : Set (Measure ℝ))
    (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K) (C : ℝ)
    (hπ : IsUniformlySuperFast 𝒟 π C)
    (ν ν' : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a : Fin K) (ha : 0 < banditGap ν a)
    (ha' : ν'.P a ∈ 𝒟)
    (hrest : ∀ k : Fin K, k ≠ a → ν'.P k = ν.P k)
    (hmean : banditOptimalMean ν < banditArmMean ν' a)
    (hKL : InformationTheory.klDiv (ν.P a) (ν'.P a) ≠ ⊤)
    (T : ℕ) (hT : 2 ≤ T) :
    (let EZ := (∑ b ∈ ExploreFirst.Asymptotic.optimalArms ν, ExploreFirst.FundIneq.expPulls ν π T b) / (T : ℝ)
     let EZ' := (∑ b ∈ ExploreFirst.Asymptotic.optimalArms ν, ExploreFirst.FundIneq.expPulls ν' π T b) / (T : ℝ)
     (EZ * Real.log (1 / EZ') - Real.log 2) /
       (InformationTheory.klDiv (ν.P a) (ν'.P a)).toReal ≤ ExploreFirst.FundIneq.expPulls ν π T a) := by sorry

end ExploreFirst.LargeT
