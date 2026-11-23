-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplitU_inv_coe
-- name    : Formalism.UG.P.afsplitU_inv_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:17.966257+00:00
-- url     : https://prove2.me/theorems/bdffff4b-a287-45d4-bac2-038e759ea1ad
-- title:
--   P: afsplit U inv coe
-- statement:
--   The P construction uses the afsplit U inv coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitC.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitC.lean#L114-L115

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
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
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "R" => E ⊗[F] 𝔸

theorem Formalism.UG.P.afsplitU_inv_coe (h : GL n Rv) (k : GL n R) :
    (((afsplitU v h k)⁻¹ : GL n R) : Matrix n n R) = afsplitC v (h⁻¹ : GL n Rv) (k⁻¹ : GL n R) := by sorry
