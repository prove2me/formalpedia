-- Prove2me | Theorems.Thm_Formalism_UG_P_inclE_injective
-- name    : Formalism.UG.P.inclE_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:03.062339+00:00
-- url     : https://prove2.me/theorems/20dc0fc9-165c-4267-a385-cff88db8071d
-- title:
--   P: incl E injective
-- statement:
--   The P construction uses the incl E injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/InclusionInjective.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/InclusionInjective.lean#L29-L33

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG

theorem Formalism.UG.P.inclE_injective (F E : Type) [Field F] [CommRing E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [Nontrivial R] :
    Function.Injective (inclE (F := F) (E := E) R) := by sorry
