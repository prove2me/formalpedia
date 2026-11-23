-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_G1_IsFrame_map
-- name    : Formalism.L2.Geo.Def.G1.IsFrame.map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:28.012808+00:00
-- url     : https://prove2.me/theorems/7be84f53-d416-4a2d-a10e-27f3b21e7b34
-- title:
--   Is Frame: map
-- statement:
--   The Is Frame construction uses the map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/DualFrame.lean#L138-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/DualFrame.lean#L138-L153

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
variable {K : Type} [Field K] [StarRing K]

theorem Formalism.L2.Geo.Def.G1.IsFrame.map {n k : ℕ} {H : Matrix (Fin n) (Fin n) K} {g w : Fin k → Fin n → K} (hf : IsFrame H g w)
    {A : Type} [CommRing A] (φ : K →+* A) (σ : A →+* A) (hσ : ∀ x, σ (φ x) = φ (star x)) (z : Fin n → A) :
    z = ∑ i, Formalism.UG.hform σ (H.map φ) (fun c => φ (w i c)) z • (fun a => φ (g i a)) := by sorry
