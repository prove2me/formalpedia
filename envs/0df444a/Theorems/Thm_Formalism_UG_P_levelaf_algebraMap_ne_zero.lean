-- Prove2me | Theorems.Thm_Formalism_UG_P_levelaf_algebraMap_ne_zero
-- name    : Formalism.UG.P.levelaf_algebraMap_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:32:44.64615+00:00
-- url     : https://prove2.me/theorems/d1e4890f-16a9-4e09-acf3-58dccc1c795c
-- title:
--   P: levelaf algebra Map ne zero
-- statement:
--   The P construction uses the levelaf algebra Map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L76-L82

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

theorem Formalism.UG.P.levelaf_algebraMap_ne_zero (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0) :
    algebraMap (𝓞 F) (v.adicCompletion F) D ≠ 0 := by sorry
