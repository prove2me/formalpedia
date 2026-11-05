-- Prove2me | Theorems.Thm_BrownianEnergyRep_notation_2_3
-- name    : BrownianEnergyRep.notation_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:03:52.679198+00:00
-- url     : https://prove2.me/theorems/faec4ff0-230e-4485-9c78-bb9528abbcf4
-- title:
--   $H(G)$ is a subgroup; $\varphi'\varphi^{-1}$ has the energy of $\varphi^{-1}\varphi'$
-- statement:
--   Let $G$ be a compact connected matrix group with an $\mathrm{Ad}_G$-invariant inner product on $\mathfrak g$, and let $0<T<\infty$. The finite energy paths form a subgroup $H(G)$ of $W(G)$. For $\varphi\in H(G)$,
--   $$
--   \varphi'\varphi^{-1}(t)=\mathrm{Ad}_{\varphi_t}\big(\varphi^{-1}\varphi'(t)\big)\quad\text{for a.e. }t,
--   $$
--   so $\varphi'\varphi^{-1}\in L^2([0,T];\mathfrak g)$ and
--   $$
--   \|\varphi\|^2_{H,T}=\int_0^T|\varphi'\varphi^{-1}(t)|^2\,dt .
--   $$
--   This makes the products and inverses in the representations legitimate, and it justifies using either logarithmic derivative in the energy.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: H(G) through ‖h‖_{H,T} < ∞ with |h⁻¹h′| in 𝔤 → entrywise absolutely continuous paths whose g-valued h⁻¹h′ (read by the inverse of incl) is in L²; reason: h⁻¹h′ is in 𝔤 for a.e. t, and on G entrywise absolute continuity is absolute continuity
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Notation 2.3(3), p.3

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `H(G)` is a subgroup of `W(G)`, and `ϕ′ϕ⁻¹ = Ad_ϕ(ϕ⁻¹ϕ′)` has the same energy (arXiv:1511.07378v1, Notation 2.3(3), p.3). -/
theorem notation_2_3 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G] [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)] :
    (∃ S : Subgroup ↥(WienerGroup G T), (S : Set ↥(WienerGroup G T)) = FiniteEnergy L T) ∧
    ∀ ϕ ∈ FiniteEnergy L T,
      (rightLog L ϕ =ᵐ[volume.restrict (Ioc 0 T)] fun t => L.Ad (pathAt ϕ t) (leftLog L ϕ t)) ∧
      MemLp (rightLog L ϕ) 2 (volume.restrict (Ioc 0 T)) ∧
      energy L ϕ = ∫ t in Ioc 0 T, ‖rightLog L ϕ t‖ ^ 2 := by sorry

end BrownianEnergyRep
