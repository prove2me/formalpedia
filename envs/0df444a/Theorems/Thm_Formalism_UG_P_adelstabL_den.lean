-- Prove2me | Theorems.Thm_Formalism_UG_P_adelstabL_den
-- name    : Formalism.UG.P.adelstabL_den
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:56:38.223797+00:00
-- url     : https://prove2.me/theorems/31241922-3ce5-4eb3-94d6-09dff3fd987a
-- title:
--   P: adelstab L den
-- statement:
--   The P construction uses the adelstab L den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AdelstabL.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AdelstabL.lean#L23-L37

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
omit [NumberField F] [Algebra F E]

theorem Formalism.UG.P.adelstabL_den {κ : Type} [Fintype κ] (f : κ → E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ i, IsIntegral ℤ ((m : E) * f i) := by sorry
