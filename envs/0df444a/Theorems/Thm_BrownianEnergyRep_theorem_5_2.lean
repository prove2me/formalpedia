-- Prove2me | Theorems.Thm_BrownianEnergyRep_theorem_5_2
-- name    : BrownianEnergyRep.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:02:20.75476+00:00
-- url     : https://prove2.me/theorems/637aecbc-70c5-4410-a21c-4b95464e441c
-- title:
--   Theorem 5.2 — rotations preserve $\Gamma$
-- statement:
--   Let $(H,W,\Gamma)$ be an abstract Wiener space. For any $R\in O(W^*)$, the map $R^*$ is a $\mathcal B(W)$-measurable map from $W$ to $W$ and
--   $$
--   \Gamma\circ(R^*)^{-1}=\Gamma .
--   $$
--   This gives the invariance of $\nu$ under the rotations $O_\varphi$.
--
--   Differences from the source:
--   - reading: R a topological homeomorphism of W* with adjoint R*: W → W → R orthogonal on H with a bounded bijection R* of W such that R*j = jR; reason: R* is defined on all of W only if the homeomorphism is weak-*; R*j = jR is the defining identity tested on j(H)
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Theorem 5.2, p.16

import Mathlib
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace
import Definitions.Def_BrownianEnergyRep_Rotation

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Theorem 5.2 (arXiv:1511.07378v1, p.16): `R*` is measurable and preserves `Γ`. -/
theorem theorem_5_2 {H W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
    (A : AbstractWienerSpace H W) (ρ : Rotation A) :
    Measurable ρ.adj ∧ A.Γ.map ρ.adj = A.Γ := by sorry

end BrownianEnergyRep
