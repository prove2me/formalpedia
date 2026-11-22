-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_Tj_eq
-- name    : Formalism.UG.P.satake_Tj_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:46.246476+00:00
-- url     : https://prove2.me/theorems/bc01fa0b-f038-4dac-a6e4-b07fc291599a
-- title:
--   P: satake Tj eq
-- statement:
--   The P construction uses the satake Tj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L36-L38

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

theorem Formalism.UG.P.satake_Tj_eq (k : Type) [CommRing k] (ϖ : v.adicCompletion F) (j : ℕ)
    (g : GL (Fin n) (v.adicCompletion F)) :
    Tj k n (Ov F v) ϖ j g = Set.indicator (satakeTset v ϖ j) 1 g := by sorry
