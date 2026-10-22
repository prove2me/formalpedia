-- Prove2me | Theorems.Thm_FiniteEnergyPlane_periodicOrbit_bridge
-- name    : FiniteEnergyPlane.periodicOrbit_bridge
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T23:26:15.328312+00:00
-- url     : https://prove2.me/theorems/345faf92-b9a1-4def-abca-858310cecd90
-- title:
--   Reeb orbits and periodic Hamiltonian orbits on star-shaped levels in $\mathbb{R}^4$
-- statement:
--   Identify $\mathbb{R}^4$ with coordinates $(q_1,p_1,q_2,p_2)$ of the `HryniewiczCriterion` setting with $V$ for $n=1$ coordinatewise, by $\iota$, and let $H=H_0\circ\iota^{-1}$. Then $S=H^{-1}(1)$ is a strictly star-shaped level in the sense of this mission if and only if $H_0^{-1}(1)$ is one in the sense of `HryniewiczCriterion`. If it is, then:
--   1. for every periodic orbit $(y,T')$ of $X_{H_0}$ on $H_0^{-1}(1)$ there is a periodic Reeb orbit $(x,T)$ of $H$ with $x(\mathbb{R})=\iota(y(\mathbb{R}))$ and $T=\int_0^{T'}\lambda_0(\iota y)\,\tfrac{d}{d\tau}(\iota y)\,d\tau$;
--   2. for every periodic Reeb orbit $(x,T)$ of $H$ there is such a periodic orbit $(y,T')$ of $X_{H_0}$ with the same image and with $T$ equal to that action.
--
--   **Formalization Note** $\iota$ is `fun x k => x (Fin.cast _ k)` from `HryniewiczCriterion.R4 = Fin 4 → ℝ` to `V 1 = Fin (2 * (1 + 1)) → ℝ`. Periodic orbits on both sides need not be simple.
-- source:
--   Compatibility with the HryniewiczCriterion setting (case $n=1$); H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Section 1

import Definitions.Def_FiniteEnergyPlane_Setting
import Definitions.Def_HryniewiczCriterion_Basic

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The case `n = 1` and `HryniewiczCriterion`. Identify `HryniewiczCriterion.R4` with `V 1`
coordinatewise (both are `(q₁, p₁, q₂, p₂)`) by `toV`, and let `H = H₀ ∘ toV⁻¹`. Then the two notions
of a strictly star-shaped level agree, and for such `H₀` every periodic orbit `(x, T)` of `X_{H₀}` on
`H₀⁻¹(1)` has, after `toV`, the same image as a periodic Reeb orbit of `H` whose period is the action
`∫₀ᵀ λ₀(x) x'`; every periodic Reeb orbit of `H` arises in this way. -/
theorem periodicOrbit_bridge (H₀ : HryniewiczCriterion.R4 → ℝ) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    (IsStrictlyStarShapedLevel H ↔ HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) ∧
      (HryniewiczCriterion.IsStrictlyStarShapedLevel H₀ →
        (∀ P : HryniewiczCriterion.PeriodicOrbit H₀, ∃ Q : ReebOrbit H,
          Set.range Q.x = Set.range (fun τ => toV (P.x τ)) ∧
            Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ)) ∧
        ∀ Q : ReebOrbit H, ∃ P : HryniewiczCriterion.PeriodicOrbit H₀,
          Set.range (fun τ => toV (P.x τ)) = Set.range Q.x ∧
            Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ)) := by
  sorry

end FiniteEnergyPlane
