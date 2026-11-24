-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_PN_latS_of_loc
-- name    : Formalism.L2.Geo.Def.PN.latS_of_loc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:23:28.374917+00:00
-- url     : https://prove2.me/theorems/bfabf81d-189c-4813-b083-afd6b55d3c2b
-- title:
--   PN: lat S of loc
-- statement:
--   The PN construction uses the lat S of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PNeatB.lean#L144-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PNeatB.lean#L144-L164

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PNeatB
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
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PN
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem Formalism.L2.Geo.Def.PN.latS_of_loc (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (w : n → 𝒜) (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun i => prV (E := E) v (w i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) :
    w ∈ latS (F := F) 𝔸 𝒮 Λ := by sorry
