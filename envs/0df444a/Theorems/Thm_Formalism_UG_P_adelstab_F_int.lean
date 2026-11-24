-- Prove2me | Theorems.Thm_Formalism_UG_P_adelstab_F_int
-- name    : Formalism.UG.P.adelstab_F_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:18.999474+00:00
-- url     : https://prove2.me/theorems/2e13ff89-12f6-4a21-a326-dea83e7baa51
-- title:
--   P: adelstab F int
-- statement:
--   The P construction uses the adelstab F int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L43-L47

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
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem Formalism.UG.P.adelstab_F_int (k : F) (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) k ∈ intAd F) :
    k ∈ (algebraMap (𝓞 F) F).range := by sorry
