-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_PC_ie_lat
-- name    : Formalism.L2.Geo.Def.PC.ie_lat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:25.233399+00:00
-- url     : https://prove2.me/theorems/8c45bc7d-44ea-4d53-a777-fd85f2c7fe8f
-- title:
--   PC: ie lat
-- statement:
--   The PC construction uses the ie lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PClassD.lean#L48-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PClassD.lean#L48-L74

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

theorem Formalism.L2.Geo.Def.PC.ie_lat (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E))
    (u : n → E ⊗[F] v.adicCompletion F) (hu : u ∈ latV v Λ) :
    (fun i => afsplitIE v (u i)) ∈ latA (F := F) Λ := by sorry
