-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_G1_dual_frame
-- name    : Formalism.L2.Geo.Def.G1.dual_frame
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:54.306948+00:00
-- url     : https://prove2.me/theorems/5ffbca7f-bfc5-474f-b293-8b5521439c7b
-- title:
--   G1: dual frame
-- statement:
--   The G1 construction uses the dual frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/DualFrame.lean#L17-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/DualFrame.lean#L17-L112

import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Matrix
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
  [IsScalarTower R K V]

theorem Formalism.L2.Geo.Def.G1.dual_frame (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    ∃ (n : ℕ) (g w : Fin n → V), (∀ i, g i ∈ L) ∧ (∀ i, w i ∈ Formalism.HermitianLatticesTheory.dual h L) ∧
      ∀ z : V, z = ∑ i, h (w i) z • g i := by sorry
