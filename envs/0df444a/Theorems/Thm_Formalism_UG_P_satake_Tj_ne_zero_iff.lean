-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_Tj_ne_zero_iff
-- name    : Formalism.UG.P.satake_Tj_ne_zero_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:03.692797+00:00
-- url     : https://prove2.me/theorems/82b4337e-e6e3-4551-b638-d68bbe94ff1a
-- title:
--   P: satake Tj ne zero iff
-- statement:
--   The P construction uses the satake Tj ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L40-L46

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

theorem Formalism.UG.P.satake_Tj_ne_zero_iff (k : Type) [CommRing k] [Nontrivial k] (ϖ : v.adicCompletion F) (j : ℕ)
    (g : GL (Fin n) (v.adicCompletion F)) :
    Tj k n (Ov F v) ϖ j g ≠ 0 ↔ g ∈ satakeTset v ϖ j := by sorry
