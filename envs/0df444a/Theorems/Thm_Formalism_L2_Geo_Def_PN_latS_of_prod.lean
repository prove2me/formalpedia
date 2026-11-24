-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_PN_latS_of_prod
-- name    : Formalism.L2.Geo.Def.PN.latS_of_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:16.582801+00:00
-- url     : https://prove2.me/theorems/a603d6f2-de2f-4d5e-acae-c8c829cfd0de
-- title:
--   PN: lat S of prod
-- statement:
--   The PN construction uses the lat S of prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PNeatB.lean#L74-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PNeatB.lean#L74-L103

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

theorem Formalism.L2.Geo.Def.PN.latS_of_prod (Λ : Submodule (𝓞 E) (n → E)) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ w : n → 𝒜, (∀ v ∈ T, (fun i => prV (E := E) v (w i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) →
    (fun i => (∏ v ∈ T, (1 - afsplitEps E v)) * w i) ∈ latS (F := F) 𝔸 𝒮 Λ →
    w ∈ latS (F := F) 𝔸 𝒮 Λ := by sorry
