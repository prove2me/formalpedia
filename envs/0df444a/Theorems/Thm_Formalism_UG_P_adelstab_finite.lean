-- Prove2me | Theorems.Thm_Formalism_UG_P_adelstab_finite
-- name    : Formalism.UG.P.adelstab_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:46.340619+00:00
-- url     : https://prove2.me/theorems/18286acf-4dac-4cce-ad80-d4ba8229e7db
-- title:
--   P: adelstab finite
-- statement:
--   The P construction uses the adelstab finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L180-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L180-L231

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

theorem Formalism.UG.P.adelstab_finite (G : GL n 𝒜) (L : Submodule 𝒮 (n → 𝒜)) (c₂ d : 𝓞 F) (hc₂ : c₂ ≠ 0)
    (hd : d ≠ 0) (hL : ∀ v ∈ L, ∀ i, levelafC E c₂ * v i ∈ 𝒮)
    (hG : ∀ i j, levelafC E d * (G : Matrix n n 𝒜) i j ∈ 𝒮) :
    Module.Finite (𝓞 E) (adelstabLam F E G L) := by sorry
