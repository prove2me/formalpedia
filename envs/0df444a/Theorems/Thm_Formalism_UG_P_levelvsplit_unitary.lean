-- Prove2me | Theorems.Thm_Formalism_UG_P_levelvsplit_unitary
-- name    : Formalism.UG.P.levelvsplit_unitary
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:35.257903+00:00
-- url     : https://prove2.me/theorems/534b1da9-5df4-4633-8d69-25f10cd2c70c
-- title:
--   P: levelvsplit unitary
-- statement:
--   The P construction uses the levelvsplit unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelvsplit.lean#L52-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelvsplit.lean#L52-L66

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
variable {B K : Type} [CommRing B] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.levelvsplit_unitary (τ : B →+* B) (φ : B ≃+* K × K)
    (hτ : ∀ x, φ (τ x) = swapR K (φ x)) (J' : Matrix n n B) (h : GL n B) (hh : h ∈ UJ τ J') :
    ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ *
        J'.map ((RingHom.fst K K).comp φ.toRingHom) *
        (h : Matrix n n B).map ((RingHom.fst K K).comp φ.toRingHom) =
      J'.map ((RingHom.fst K K).comp φ.toRingHom) := by sorry
