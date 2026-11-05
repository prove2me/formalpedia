-- Prove2me | Theorems.Thm_BrownianEnergyRep_path_abstract_wiener_space
-- name    : BrownianEnergyRep.path_abstract_wiener_space
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:05:40.476135+00:00
-- url     : https://prove2.me/theorems/3e427bea-2278-4466-a18b-c8c8b7cf5079
-- title:
--   $(H(\mathfrak g),W(\mathfrak g),\nu)$ is an abstract Wiener space and $O_\varphi$ is a rotation
-- statement:
--   $(H(\mathfrak g),W(\mathfrak g),\nu)$ is an abstract Wiener space. Writing $H(\mathfrak g)$ as $L^2([0,T];\mathfrak g)$, the variable $\langle a,\cdot\rangle$ is the Wiener integral $I(a)$. For $\varphi\in H(G)$, the map $a\mapsto\mathrm{Ad}_\varphi a$ is an orthogonal transformation of $H(\mathfrak g)$ whose adjoint in the sense of Notation 5.1 is $O_\varphi$. This places the energy representation in the setting of Proposition 5.5.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: H(G) through ‖h‖_{H,T} < ∞ with |h⁻¹h′| in 𝔤 → entrywise absolutely continuous paths whose g-valued h⁻¹h′ (read by the inverse of incl) is in L²; reason: h⁻¹h′ is in 𝔤 for a.e. t, and on G entrywise absolute continuity is absolute continuity
--   - encoding: the Wiener measure ν on W(𝔤), not spelled out → centred Gaussian with Cov(⟨a,w_s⟩,⟨b,w_t⟩) = ⟨a,b⟩ min(s,t); reason: the condition is basis-free and determines ν
--   - encoding: O_ϕ(w) = ∫₀^· Ad_ϕ δw_s → pathwise by parts: Ad_{ϕ_t}w_t − ∫₀ᵗ Ad_{ϕ_s}[ϕ⁻¹ϕ′(s),w_s]ds; reason: ϕ is absolutely continuous; this equals the stochastic integral ν-a.e. and is defined for every w
--   - encoding: the integral ∫₀ᵀ⟨a,dw_s⟩ → the L²(ν) limit along step functions, as a representative chosen by Classical.epsilon; reason: it is unique ν-a.e. by wiener_integral_isometry
--   - encoding: the Cameron-Martin space H(𝔤) of paths → L²([0,T];𝔤) through a ↦ ∫₀^·a; reason: this embedding is an isometry for the norm of H(𝔤)
--   - reading: R a topological homeomorphism of W* with adjoint R*: W → W → R orthogonal on H with a bounded bijection R* of W such that R*j = jR; reason: R* is defined on all of W only if the homeomorphism is weak-*; R*j = jR is the defining identity tested on j(H)
--   - encoding: ⟨h,w⟩ for h ∈ H → the L²(Γ) limit, as a representative chosen by Classical.epsilon (pairing); reason: unique a.e. by pairing_isometry
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, proof of Theorem 5.8, p.19

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_rotation__ef917c
import Definitions.Def_BrownianEnergyRep_wienerIntegral
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace_pairing
import Definitions.Def_BrownianEnergyRep_Rotation
import Definitions.Def_BrownianEnergyRep_IsPathWienerSpace

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `(H(𝔤), W(𝔤), ν)` is an abstract Wiener space, `⟨a,·⟩` is the Wiener integral, and `O_ϕ` is
the adjoint of the rotation `a ↦ Ad_ϕ a` (arXiv:1511.07378v1, proof of Theorem 5.8, p.19). -/
theorem path_abstract_wiener_space {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G]
    [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)] :
    (∃ A : AbstractWienerSpace (Lp E 2 (volume.restrict (Ioc (0 : ℝ) T))) ↥(WienerPath E T),
      IsPathWienerSpace A) ∧
    ∀ A : AbstractWienerSpace (Lp E 2 (volume.restrict (Ioc (0 : ℝ) T))) ↥(WienerPath E T),
      IsPathWienerSpace A →
      (∀ a, A.pairing a =ᵐ[A.Γ] wienerIntegral A.Γ a) ∧
      ∀ ϕ ∈ FiniteEnergy L T, ∃ ρ : Rotation A, (∀ w, ρ.adj w = rotation L ϕ w) ∧
        ∀ a, (ρ.R a : ℝ → E) =ᵐ[volume.restrict (Ioc 0 T)]
          fun s => L.Ad (pathAt ϕ s) ((a : ℝ → E) s) := by sorry

end BrownianEnergyRep
