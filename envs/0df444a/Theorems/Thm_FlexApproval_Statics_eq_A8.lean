-- Prove2me | Theorems.Thm_FlexApproval_Statics_eq_A8
-- name    : FlexApproval.Statics.eq_A8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:44.623633+00:00
-- url     : https://prove2.me/theorems/fbdfd3ac-0136-4b18-ab4a-bef1fad5bab4
-- title:
--   Eq. (A.8), p. 33 — implicit function theorem: ∂α*/∂x = −(∂V′(α*)/∂x)/(∂V′(α*)/∂α), with negative denominator
-- statement:
--   Let $x\mapsto P(x)$ be a family of parameter vectors of the drug-approval model indexed by a real parameter $x$ ranging over an open set $s$, each satisfying the standing assumptions, such that $(x,\alpha)\mapsto V'_{P(x)}(\alpha)$ is continuously differentiable on $s\times(0,1)$. Let $\alpha^*(x)$ be an optimal approval policy for $P(x)$, for every $x\in s$. Then at every $x_0\in s$,
--   $$\frac{\partial V'(\alpha^*)}{\partial\alpha}<0\qquad\text{and}\qquad \frac{\partial\alpha^*}{\partial x}(x_0)=-\frac{\partial V'(\alpha^*)/\partial x}{\partial V'(\alpha^*)/\partial\alpha},$$
--   with both partial derivatives taken at $(x_0,\alpha^*(x_0))$; in particular $\alpha^*$ is differentiable at $x_0$.
--
--   So the sign of $\partial\alpha^*/\partial x$ is the sign of $\partial V'(\alpha^*)/\partial x$, which (A.10)–(A.20) compute for each parameter.
--
--   **Formalization Note** $V'$ is `deriv (V P)`. The continuous differentiability of $(x,\alpha)\mapsto V'_{P(x)}(\alpha)$ is the smoothness the Implicit Function Theorem needs; the paper uses it without stating it. It holds for the families that change one field of a fixed parameter vector.
-- source:
--   Bravo, Corcoran & Long, Flexible Drug Approval Policies, SSRN working paper 3027263 (version of 17 Jul 2019), p. 33, proof of Proposition 1, Eq. (A.8)

import Mathlib
import Definitions.Def_FlexApproval_Statics_Model

namespace FlexApproval.Statics

/-- Eq. (A.8), p. 33 (implicit function theorem). Let `x ↦ Pf x` be a family of parameter vectors
on an open set `s` of values of a parameter `x`, all satisfying the standing assumptions, such that
`(x, α) ↦ V′_{Pf x}(α)` is continuously differentiable on `s × (0, 1)`, and let `aS x` be an optimal
policy for `Pf x`. Then at every `x₀ ∈ s` the denominator `∂V′(α*)/∂α` is negative and
`∂α*/∂x = −(∂V′(α*)/∂x) / (∂V′(α*)/∂α)`. -/
theorem eq_A8 (Pf : ℝ → Params) (s : Set ℝ) (hs : IsOpen s) (hst : ∀ x ∈ s, (Pf x).Standing)
    (hW : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => deriv (V (Pf q.1)) q.2) (s ×ˢ Set.Ioo (0 : ℝ) 1))
    (aS : ℝ → ℝ) (haS : ∀ x ∈ s, IsOptimal (Pf x) (aS x)) (x₀ : ℝ) (hx₀ : x₀ ∈ s) :
    deriv (fun α => deriv (V (Pf x₀)) α) (aS x₀) < 0 ∧
    HasDerivAt aS
      (-(deriv (fun x => deriv (V (Pf x)) (aS x₀)) x₀) /
        deriv (fun α => deriv (V (Pf x₀)) α) (aS x₀)) x₀ := by sorry

end FlexApproval.Statics
