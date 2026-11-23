-- Prove2me | Theorems.Thm_Formalism_UG_P_levelaf_adele_denom
-- name    : Formalism.UG.P.levelaf_adele_denom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:29.821796+00:00
-- url     : https://prove2.me/theorems/94582def-114e-4a6a-8700-b6057db3be85
-- title:
--   P: levelaf adele denom
-- statement:
--   The P construction uses the levelaf adele denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L47-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L47-L59

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

theorem Formalism.UG.P.levelaf_adele_denom (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d * a ∈ intAd F := by sorry
