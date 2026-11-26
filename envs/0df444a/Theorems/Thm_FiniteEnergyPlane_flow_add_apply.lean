-- Prove2me | Theorems.Thm_FiniteEnergyPlane_flow_add_apply
-- name    : FiniteEnergyPlane.flow_add_apply
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T21:43:58.436633+00:00
-- url     : https://prove2.me/theorems/c0a2cf00-676c-44dc-b285-3724e787d9d0
-- title:
--   Group law of a compactly supported planar flow
-- statement:
--   Let $X$ be a smooth compactly supported vector field on $\mathbb{C}$ and let $\psi$ be a flow of $X$: $\psi_0 = \mathrm{id}$ and $\partial_s\psi_s(y) = X(\psi_s y)$ for all $s, y$. Then $\psi_s(\psi_r y) = \psi_{s+r}(y)$ for all $s, r \in \mathbb{R}$ and $y \in \mathbb{C}$.
--
--   Role: reusable group law for the complete flows of compactly supported fields (e.g. the platform's FlowCalculus flows).
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), § 3.2

import Mathlib

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Group law of the flow of a smooth compactly supported vector field on `ℂ`: if `ψ` is a flow of `X`
(`ψ_0 = id` and `∂ₛ ψ_s y = X(ψ_s y)`), then `ψ_s ∘ ψ_r = ψ_{s+r}`. -/
theorem flow_add_apply (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (hXK : HasCompactSupport X)
    (ψ : ℝ → ℂ → ℂ) (hψ0 : ∀ y, ψ 0 y = y)
    (hψd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) (s r : ℝ) (y : ℂ) :
    ψ s (ψ r y) = ψ (s + r) y := by
  sorry

end FiniteEnergyPlane
