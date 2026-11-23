-- Prove2me | Theorems.Thm_Formalism_UG_P_adelstab_mem_iff
-- name    : Formalism.UG.P.adelstab_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:40.181863+00:00
-- url     : https://prove2.me/theorems/304d5cde-f288-4750-93a9-332794ab4a5b
-- title:
--   P: adelstab mem iff
-- statement:
--   The P construction uses the adelstab mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L129-L130

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

theorem Formalism.UG.P.adelstab_mem_iff (G : GL n 𝒜) (L : Submodule 𝒮 (n → 𝒜)) (x : n → E) :
    x ∈ adelstabLam F E G L ↔ ((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) ∈ L := by sorry
