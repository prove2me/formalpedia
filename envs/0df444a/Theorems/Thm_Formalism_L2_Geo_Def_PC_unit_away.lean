-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_PC_unit_away
-- name    : Formalism.L2.Geo.Def.PC.unit_away
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:20.58333+00:00
-- url     : https://prove2.me/theorems/caa2925a-b84a-42be-bda6-c3d70e0fd1cc
-- title:
--   PC: unit away
-- statement:
--   The PC construction uses the unit away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PClassD.lean#L76-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PClassD.lean#L76-L112

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem Formalism.L2.Geo.Def.PC.unit_away (D : 𝓞 F) (hD : D ≠ 0) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (u : 𝔸), u ∈ intAd F ∧
      (1 : 𝔸) = algebraMap (𝓞 F) 𝔸 D * u + ∑ v ∈ T, afsplitI v 1 := by sorry
