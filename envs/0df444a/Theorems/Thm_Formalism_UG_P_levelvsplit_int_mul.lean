-- Prove2me | Theorems.Thm_Formalism_UG_P_levelvsplit_int_mul
-- name    : Formalism.UG.P.levelvsplit_int_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:18.301069+00:00
-- url     : https://prove2.me/theorems/c01a368d-af41-4d46-bd6e-b352e557ab70
-- title:
--   P: levelvsplit int mul
-- statement:
--   The P construction uses the levelvsplit int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelvsplit.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelvsplit.lean#L80-L85

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

theorem Formalism.UG.P.levelvsplit_int_mul {S : Type} [SetLike S K] [SubringClass S K] (O : S)
    (M N : Matrix n n K) (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O) :
    ∀ i j, (M * N) i j ∈ O := by sorry
