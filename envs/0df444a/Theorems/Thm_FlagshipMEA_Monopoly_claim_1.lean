-- Prove2me | Theorems.Thm_FlagshipMEA_Monopoly_claim_1
-- name    : FlagshipMEA.Monopoly.claim_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:19.224981+00:00
-- url     : https://prove2.me/theorems/8fd59b91-b67a-4bb7-9d8a-0880b3dd71d7
-- title:
--   Claim 1 — two values and a slope determine a nonconstant hyperbola
-- statement:
--   Consider two nonconstant rational curves $h(x)=(\beta_1+\beta_2x)/(\beta_3+x)$ and $\tilde h(x)=(\gamma_1+\gamma_2x)/(\gamma_3+x)$, each defined to the right of its pole at points $x_1<x_2$. If their values agree at both points and their derivatives agree at $x_2$, then their coefficients agree:
--
--   $$h(x_1)=\tilde h(x_1),\quad h(x_2)=\tilde h(x_2),\quad h'(x_2)=\tilde h'(x_2)\quad\Longrightarrow\quad(\beta_1,\beta_2,\beta_3)=(\gamma_1,\gamma_2,\gamma_3).$$
--
--   The claim is an identifiability statement used in the paper's discussion of tied MEA indices. **Formalization Note** Nonconstancy, $\beta_1\ne\beta_2\beta_3$ and $\gamma_1\ne\gamma_2\gamma_3$, is necessary: a constant curve does not identify its pole parameter.
-- source:
--   He, Ke & Zhang, A Model of Product Line Marketing, SSRN 3631879 (version of August 2021), pp. 42–43 (PDF 44–45), Claim 1

import Mathlib

namespace FlagshipMEA.Monopoly

/-- Claim 1 (pp. 42–43), pinned to nonconstant hyperbolas: two values and
one derivative determine all three coefficients. -/
theorem claim_1 (β₁ β₂ β₃ γ₁ γ₂ γ₃ m₁ m₂ : ℝ)
    (hβ : β₁ ≠ β₂ * β₃) (hγ : γ₁ ≠ γ₂ * γ₃)
    (hβdom : -β₃ < m₁) (hγdom : -γ₃ < m₁) (h12 : m₁ < m₂)
    (hval1 : (β₁ + β₂ * m₁) / (β₃ + m₁) =
      (γ₁ + γ₂ * m₁) / (γ₃ + m₁))
    (hval2 : (β₁ + β₂ * m₂) / (β₃ + m₂) =
      (γ₁ + γ₂ * m₂) / (γ₃ + m₂))
    (hslope : deriv (fun x : ℝ => (β₁ + β₂ * x) / (β₃ + x)) m₂ =
      deriv (fun x : ℝ => (γ₁ + γ₂ * x) / (γ₃ + x)) m₂) :
    β₁ = γ₁ ∧ β₂ = γ₂ ∧ β₃ = γ₃ := by sorry

end FlagshipMEA.Monopoly
