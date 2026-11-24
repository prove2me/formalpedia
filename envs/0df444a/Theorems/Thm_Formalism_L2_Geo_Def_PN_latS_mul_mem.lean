-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_PN_latS_mul_mem
-- name    : Formalism.L2.Geo.Def.PN.latS_mul_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:50.329454+00:00
-- url     : https://prove2.me/theorems/ec04c038-0a31-4c5e-9725-2b85282be498
-- title:
--   PN: lat S mul mem
-- statement:
--   The PN construction uses the lat S mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PNeatB.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PNeatB.lean#L19-L22

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

theorem Formalism.L2.Geo.Def.PN.latS_mul_mem {R : Type} [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R))
    (Λ : Submodule (𝓞 E) (n → E)) {c : E ⊗[F] R} (hc : c ∈ S) {w : n → E ⊗[F] R}
    (hw : w ∈ latS (F := F) R S Λ) : (fun i => c * w i) ∈ latS (F := F) R S Λ := by sorry
