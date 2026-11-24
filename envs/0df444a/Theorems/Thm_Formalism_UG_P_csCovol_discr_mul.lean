-- Prove2me | Theorems.Thm_Formalism_UG_P_csCovol_discr_mul
-- name    : Formalism.UG.P.csCovol_discr_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:32:28.233477+00:00
-- url     : https://prove2.me/theorems/568a392b-a729-4e18-9660-8e3fb974ee2e
-- title:
--   P: cs Covol discr mul
-- statement:
--   The P construction uses the cs Covol discr mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsCovol.lean#L58-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsCovol.lean#L58-L76

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P

theorem Formalism.UG.P.csCovol_discr_mul {K : Type} [Field K] [NumberField K] (z : K)
    (hz : ∀ a : 𝓞 K, Algebra.trace ℚ K ((a : K) * z) ∈ Set.range (algebraMap ℤ ℚ)) :
    ((discr K : ℚ) : K) * z ∈ Set.range (algebraMap (𝓞 K) K) := by sorry
