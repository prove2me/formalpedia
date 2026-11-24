-- Prove2me | Theorems.Thm_Formalism_UG_P_adelstab_stab
-- name    : Formalism.UG.P.adelstab_stab
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:20.522033+00:00
-- url     : https://prove2.me/theorems/00f20665-bb4b-4be8-8cdc-eef4048cea51
-- title:
--   P: adelstab stab
-- statement:
--   The P construction uses the adelstab stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L132-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L132-L141

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem Formalism.UG.P.adelstab_stab (G : GL n 𝒜) (L : Submodule 𝒮 (n → 𝒜)) (γ₀ : GL n E)
    (hM : G⁻¹ * bc ι γ₀ * G ∈ stabGL L) : γ₀ ∈ stabGL (adelstabLam F E G L) := by sorry
