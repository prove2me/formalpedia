-- Prove2me | Theorems.Thm_BanditCovariates_ABSE_theorem_5_1_alpha_infty
-- name    : BanditCovariates.ABSE.theorem_5_1_alpha_infty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:09:48.992688+00:00
-- url     : https://prove2.me/theorems/6a3637de-6f0d-4838-893e-9e724242d4d6
-- title:
--   Theorem 5.1 (α = ∞), p. 22 — ABSE has 𝔼Rₙ ≤ CK log n
-- statement:
--   Fix $d\ge1$, $0<\beta\le1$, $L>0$, $0<\delta_0<1$ and $0<\underline c\le\bar c$. There is a constant $C>0$, depending only on these parameters, such that the following holds for every $K\ge2$ and every horizon $n\ge K\log K$. Consider a $K$-armed bandit machine with covariates in $\mathcal X=[0,1]^d$ (§3.1) whose arm means are $(\beta,L)$-Hölder for the Euclidean norm, whose covariate law has a density between $\underline c$ and $\bar c$, and which satisfies the margin condition with $\alpha=\infty$:
--
--   $$P_X\big(0<f^\star(X)-f^\sharp(X)\le\delta_0\big)=0.$$
--
--   Then the adaptively binned successive elimination policy $\tilde\pi$ (Policy 3, run with parameters $n$, $c_0=2Ld^{\beta/2}$ and $k_0$) satisfies
--
--   $$\mathbb E R_n(\tilde\pi)\le C\,K\log n.$$
--
--   With a gap bounded away from zero wherever the best arm is unique, the regret grows only logarithmically in the horizon, as in a static bandit.
--
--   **Formalization Note** The page does not define the margin condition at $\alpha=\infty$; it is read as the limit of $C_0\delta^\alpha$ for $\delta<1$, i.e. zero mass of the region $0<f^\star-f^\sharp\le\delta_0$. The constant is quantified after the class parameters and before $K$, $n$ and the machine.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 22, Theorem 5.1, α = ∞ clause; margin condition at α = ∞ read as in paper.md slip 14

import Mathlib
import Definitions.Def_BanditCovariates_ABSE_Policy

noncomputable section

namespace BanditCovariates.ABSE

/-- Theorem 5.1, p. 22, the α = ∞ clause: the margin condition is read as
`P_X(0 < f⋆ − f♯ ≤ δ₀) = 0` for some `δ₀ ∈ (0,1)`. -/
theorem theorem_5_1_alpha_infty (d : ℕ) (β L δ₀ cLow cHigh : ℝ)
    (hd : 1 ≤ d) (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 < L)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ < 1)
    (hcLow : 0 < cLow) (hcHigh : cLow ≤ cHigh) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K n : ℕ) (hK : 2 ≤ K),
      (K : ℝ) * Real.log (K : ℝ) ≤ (n : ℝ) →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (M : Machine d K Ω),
        IsMachine M → HasDensityBounds M cLow cHigh → IsHolder M β L →
        M.PX {x | 0 < fStar M x - fSharp M x ∧ fStar M x - fSharp M x ≤ δ₀} = 0 →
        regret (n := n) M (by omega) β L ≤
          C * (K : ℝ) * Real.log (n : ℝ) := by sorry

end BanditCovariates.ABSE
