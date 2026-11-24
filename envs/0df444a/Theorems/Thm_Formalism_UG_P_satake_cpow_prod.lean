-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_cpow_prod
-- name    : Formalism.UG.P.satake_cpow_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:20.054619+00:00
-- url     : https://prove2.me/theorems/f6873cc8-a0fb-4532-85f1-c605f37884da
-- title:
--   P: satake cpow prod
-- statement:
--   The P construction uses the satake cpow prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L90-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L90-L95

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

theorem Formalism.UG.P.satake_cpow_prod {ι : Type} (x : ℂ) (hx : x ≠ 0) (s : Finset ι) (f : ι → ℂ) :
    ∏ i ∈ s, x ^ f i = x ^ (∑ i ∈ s, f i) := by sorry
