-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_Tset_left
-- name    : Formalism.UG.P.satake_Tset_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:02.500531+00:00
-- url     : https://prove2.me/theorems/a3c19648-70e6-4c41-a1b1-0696e78af491
-- title:
--   P: satake Tset left
-- statement:
--   The P construction uses the satake Tset left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L30-L34

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem Formalism.UG.P.satake_Tset_left {ϖ : v.adicCompletion F} {j : ℕ} {g k : GL (Fin n) (v.adicCompletion F)}
    (hg : g ∈ satakeTset v ϖ j) (hk : k ∈ GLint (Fin n) (Ov F v)) : k * g ∈ satakeTset v ϖ j := by sorry
