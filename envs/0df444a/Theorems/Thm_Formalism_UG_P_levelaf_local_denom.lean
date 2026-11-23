-- Prove2me | Theorems.Thm_Formalism_UG_P_levelaf_local_denom
-- name    : Formalism.UG.P.levelaf_local_denom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:30.461703+00:00
-- url     : https://prove2.me/theorems/18c05196-5e09-4251-b551-fadafbd21685
-- title:
--   P: levelaf local denom
-- statement:
--   The P construction uses the levelaf local denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L24-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L24-L42

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
variable {F : Type} [Field F] [NumberField F]

theorem Formalism.UG.P.levelaf_local_denom (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ algebraMap (𝓞 F) (v.adicCompletion F) d * x ∈ v.adicCompletionIntegers F := by sorry
