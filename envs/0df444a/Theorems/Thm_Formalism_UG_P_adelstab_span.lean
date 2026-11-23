-- Prove2me | Theorems.Thm_Formalism_UG_P_adelstab_span
-- name    : Formalism.UG.P.adelstab_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:45.941276+00:00
-- url     : https://prove2.me/theorems/407564cf-eb61-44d2-b444-8b753779bc83
-- title:
--   P: adelstab span
-- statement:
--   The P construction uses the adelstab span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L143-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L143-L167

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

theorem Formalism.UG.P.adelstab_span (G : GL n 𝒜) (L : Submodule 𝒮 (n → 𝒜)) (c₁ d : 𝓞 F) (hc₁ : c₁ ≠ 0)
    (hd : d ≠ 0) (hL : ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) → (fun i => levelafC E c₁ * v i) ∈ L)
    (hG : ∀ i j, levelafC E d * ((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) i j ∈ 𝒮) :
    Submodule.span E (adelstabLam F E G L : Set (n → E)) = ⊤ := by sorry
