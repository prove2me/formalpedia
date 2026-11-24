-- Prove2me | Theorems.Thm_Formalism_UG_P_prod_pow_sub_one_ne_zero
-- name    : Formalism.UG.P.prod_pow_sub_one_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:36.422685+00:00
-- url     : https://prove2.me/theorems/b5631424-f96b-4163-a0a0-7b1ef9d0fe85
-- title:
--   P: prod pow sub one ne zero
-- statement:
--   The P construction uses the prod pow sub one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L54-L60

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

theorem Formalism.UG.P.prod_pow_sub_one_ne_zero {q : ℤ} (hq : 2 ≤ q) {j n : ℕ} (hj : j ≤ n) :
    ∏ i ∈ Finset.range j, (q ^ (n - i) - 1) ≠ 0 := by sorry
