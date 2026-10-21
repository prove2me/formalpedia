-- Prove2me | Theorems.Thm_CrowdContest_Pooling_lemma_3
-- name    : CrowdContest.Pooling.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:27.335234+00:00
-- url     : https://prove2.me/theorems/36b8c552-fca3-48b3-811b-fc7ba652b229
-- title:
--   Lemma 3, p. 16 — an interior symmetric equilibrium of the joint contest satisfies C°′(e°*) = A h°(ξ°;n)
-- statement:
--   Let $n\ge 2$, let the random factors have a symmetric log-concave density $\psi$ (so $\xi^\circ=\xi^1+\xi^2$ has density $\psi^\circ$), let $A$ be the grand prize and $C_1,C_2$ cost functions. If $(s_1,s_2)$ with $s_1,s_2>0$ is a symmetric equilibrium of the joint contest — no pair of nonnegative efforts $(e_1,e_2)$ earns a higher expected payoff $A\,W_{\psi^\circ}\big((e_1+e_2)-(s_1+s_2)\big)-C_1(e_1)-C_2(e_2)$ against $(s_1,s_2)$ — then the aggregate cost $C^\circ$ is differentiable at the aggregate effort $e^{\circ*}=s_1+s_2$ and
--   $$C^{\circ\prime}(e^{\circ*})=A\,h^\circ(\xi^\circ;n),$$
--   i.e. $e^{\circ*}(n)=C^{\circ\prime-1}(A\,h^\circ(\xi^\circ;n))$.
--
--   This is the equilibrium characterization of the joint contest, analogous to Lemma 1 with the total prize $A$ and the density $\psi^\circ$.
--
--   **Formalization Note** Joint-contest strategies are effort pairs, as in the model (p. 14); the page's reduction to an aggregate-effort strategy is part of what is to be proved. Both equilibrium efforts are assumed positive (interiority, footnote 8). The inverse $C^{\circ\prime-1}$ is replaced by the inverse-free derivative identity.
-- source:
--   Hu & Wang, Joint vs. Separate Crowdsourcing Contests, authors' accepted manuscript (TSpace; SSRN 2892683; Manag. Sci. doi:10.1287/mnsc.2020.3683), Lemma 3, p. 16; proof OA p. 2

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

open MeasureTheory

namespace CrowdContest.Pooling

/-- Lemma 3, p. 16: at a symmetric equilibrium `(s₁, s₂)` of the joint contest with grand prize `A`
and interior efforts `s₁, s₂ > 0`, the aggregate effort `e°* = s₁ + s₂` satisfies
`C°'(e°*) = A h°(ξ°; n)`, i.e. `e°* = C°'⁻¹(A h°(ξ°; n))`. -/
theorem lemma_3 (n : ℕ) (hn : 2 ≤ n) (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ)
    (A : ℝ) (C₁ C₂ : ℝ → ℝ) (hC₁ : IsCost C₁) (hC₂ : IsCost C₂) (s₁ s₂ : ℝ)
    (hs : IsSymEqJoint ψ n A C₁ C₂ s₁ s₂) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    HasDerivAt (aggCost C₁ C₂) (A * hFun (convDensity ψ) n) (s₁ + s₂) := by sorry

end CrowdContest.Pooling
