-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_Tset_right
-- name    : Formalism.UG.P.satake_Tset_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:56.394808+00:00
-- url     : https://prove2.me/theorems/49835ec9-9a4c-436c-a5c5-24fce922303d
-- title:
--   P: satake Tset right
-- statement:
--   The P construction uses the satake Tset right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L24-L28

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

theorem Formalism.UG.P.satake_Tset_right {ϖ : v.adicCompletion F} {j : ℕ} {g k : GL (Fin n) (v.adicCompletion F)}
    (hg : g ∈ satakeTset v ϖ j) (hk : k ∈ GLint (Fin n) (Ov F v)) : g * k ∈ satakeTset v ϖ j := by sorry
