-- Prove2me | Theorems.Thm_Formalism_UG_P_levelaf_adele_res
-- name    : Formalism.UG.P.levelaf_adele_res
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:29.396801+00:00
-- url     : https://prove2.me/theorems/2ac774c8-6e68-4031-b298-17ea9b506690
-- title:
--   P: levelaf adele res
-- statement:
--   The P construction uses the levelaf adele res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L84-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L84-L153

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

theorem Formalism.UG.P.levelaf_adele_res (D : 𝓞 F) (hD : D ≠ 0) :
    ∃ T : Set (FiniteAdeleRing (𝓞 F) F), T.Finite ∧ T ⊆ intAd F ∧
      ∀ a ∈ intAd F, ∃ t ∈ T, ∃ y ∈ intAd F, a = t + algebraMap (𝓞 F) _ D * y := by sorry
