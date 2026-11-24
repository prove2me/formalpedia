-- Prove2me | Theorems.Thm_Formalism_UG_P_levelv_nsmul_inj
-- name    : Formalism.UG.P.levelv_nsmul_inj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:42.153089+00:00
-- url     : https://prove2.me/theorems/0ee0c8d0-baf6-4520-893c-8fce877287c0
-- title:
--   P: levelv nsmul inj
-- statement:
--   The P construction uses the levelv nsmul inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L252-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L252-L262

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
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
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.levelv_nsmul_inj {N : ℕ} (hN : N ≠ 0) (y y' : n → E ⊗[F] v.adicCompletion F)
    (h : N • y = N • y') : y = y' := by sorry
