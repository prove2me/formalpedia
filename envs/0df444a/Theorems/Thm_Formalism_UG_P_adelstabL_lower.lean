-- Prove2me | Theorems.Thm_Formalism_UG_P_adelstabL_lower
-- name    : Formalism.UG.P.adelstabL_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:59:03.454807+00:00
-- url     : https://prove2.me/theorems/c7e12309-f424-4f6d-a369-3b6d8fa6363a
-- title:
--   P: adelstab L lower
-- statement:
--   The P construction uses the adelstab L lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AdelstabL.lean#L81-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AdelstabL.lean#L81-L121

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
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

theorem Formalism.UG.P.adelstabL_lower (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) →
      (fun i => levelafC E c * v i) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by sorry
