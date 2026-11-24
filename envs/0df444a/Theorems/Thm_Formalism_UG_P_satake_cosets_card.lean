-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_cosets_card
-- name    : Formalism.UG.P.satake_cosets_card
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:32:54.578391+00:00
-- url     : https://prove2.me/theorems/03de7b1b-069c-4807-be22-4421ea23dda4
-- title:
--   P: satake cosets card
-- statement:
--   The P construction uses the satake cosets card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L62-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L62-L88

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

theorem Formalism.UG.P.satake_cosets_card (hTjCosets : TjCosets) {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v)
    (hu : IsUnifV F v ϖ) {j : ℕ} (hj : j ≤ n) :
    {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) | x.out ∈ satakeTset v ϖ j}.Finite ∧
    {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) | x.out ∈ satakeTset v ϖ j}.ncard =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, qV F v ^ satakeInv Finset.univ S := by sorry
