-- Prove2me | Theorems.Thm_BrownianEnergyRep_theorem_2_9
-- name    : BrownianEnergyRep.theorem_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:03:42.173279+00:00
-- url     : https://prove2.me/theorems/7edc9fe0-06fc-49fd-9ece-95b32ba08754
-- title:
--   Theorem 2.9 — $B^L$ and $B^R$ are standard $\mathfrak g$-valued Brownian motions
-- statement:
--   Under Wiener measure $\mu$, the Stratonovich integrals
--   $$
--   B^L_t=\int_0^tg_\tau^{-1}\delta g_\tau,\qquad B^R_t=\int_0^t\delta g_\tau g_\tau^{-1}
--   $$
--   exist as maps into $W(\mathfrak g)$. Each of them has law $\nu$, and its increments after time $s$ are independent of $\mathcal B_s$. So they are standard $\mathfrak g$-valued Brownian motions with covariances determined by $\langle\cdot,\cdot\rangle$. They are the maps that transfer the Brownian representations to the linear space $W(\mathfrak g)$.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: p_t = e^{tΔ/2}δ_e, the fundamental solution of (2.1), for a bi-invariant Haar measure dx → hypotheses IsHeatKernel L m p (p jointly smooth on (0,∞)×G, (2.1) pointwise for t > 0, ∫p_t f dm → f(e) for continuous f) for a Haar measure m, and μ given by IsWienerMeasure m p T μ; reason: these conditions determine p_t for t > 0 (theorem_2_1); (2.2) does not depend on the normalization of m; a Haar measure on a compact group is bi-invariant
--   - encoding: the Wiener measure ν on W(𝔤), not spelled out → centred Gaussian with Cov(⟨a,w_s⟩,⟨b,w_t⟩) = ⟨a,b⟩ min(s,t); reason: the condition is basis-free and determines ν
--   - encoding: Stratonovich and Itô integrals against semimartingales → limits in probability of trapezoidal and left-point sums along every partition sequence with mesh → 0, entrywise for matrices; reason: these are the standard characterizations of the integrals
--   - encoding: B^L, B^R μ-a.e. defined maps → AEMeasurable maps W(G) → W(𝔤) that satisfy the limit predicates; reason: such a map is determined μ-a.e. by the predicates and path continuity
--   - encoding: standard 𝔤-valued Brownian motion for the filtration → law ν and independence of increments from 𝓑_s; reason: these two properties are the definition, and continuity is part of W(𝔤)
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Theorem 2.9, p.5; Definition 2.8, p.5

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_IsHeatKernel
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_IsWienerMeasure
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_IsGaussianWienerMeasure
import Definitions.Def_BrownianEnergyRep_canonicalFiltration
import Definitions.Def_BrownianEnergyRep_IsLeftItoMap
import Definitions.Def_BrownianEnergyRep_IsRightItoMap

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Theorem 2.9 (arXiv:1511.07378v1, p.5): `B^L` and `B^R` exist and are standard `𝔤`-valued Brownian motions. -/
theorem theorem_2_9 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G] [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)]
    (m : Measure ↥G) [m.IsHaarMeasure] (p : ℝ → ↥G → ℝ) (hp : IsHeatKernel L m p)
    (μ : Measure ↥(WienerGroup G T)) (hμ : IsWienerMeasure m p T μ)
    (ν : Measure ↥(WienerPath E T)) (hν : IsGaussianWienerMeasure E T ν) :
    (∃ B, IsLeftItoMap L μ B) ∧ (∃ B, IsRightItoMap L μ B) ∧
    ∀ B, IsLeftItoMap L μ B ∨ IsRightItoMap L μ B →
      μ.map B = ν ∧
      ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
        Indep (MeasurableSpace.comap (fun γ => wAt (B γ) t - wAt (B γ) s) (borel E))
          (canonicalPast G T s) μ := by sorry

end BrownianEnergyRep
