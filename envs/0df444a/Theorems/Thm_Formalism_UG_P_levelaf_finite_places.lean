-- Prove2me | Theorems.Thm_Formalism_UG_P_levelaf_finite_places
-- name    : Formalism.UG.P.levelaf_finite_places
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:16.007357+00:00
-- url     : https://prove2.me/theorems/2f91abf7-bf3b-4c6e-bfef-93cbc06c42f3
-- title:
--   P: levelaf finite places
-- statement:
--   The P construction uses the levelaf finite places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L67-L74

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

theorem Formalism.UG.P.levelaf_finite_places (D : 𝓞 F) (hD : D ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1}.Finite := by sorry
