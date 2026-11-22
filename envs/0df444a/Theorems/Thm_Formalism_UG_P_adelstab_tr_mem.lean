-- Prove2me | Theorems.Thm_Formalism_UG_P_adelstab_tr_mem
-- name    : Formalism.UG.P.adelstab_tr_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:58:51.222628+00:00
-- url     : https://prove2.me/theorems/b9430f60-dad2-48d0-b96f-694215e9eb46
-- title:
--   P: adelstab tr mem
-- statement:
--   The P construction uses the adelstab tr mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L53-L59

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

theorem Formalism.UG.P.adelstab_tr_mem (e : E) (he : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e ∈ 𝒮) (b : 𝓞 E) :
    Algebra.trace F E (e * algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 F) F).range := by sorry
