-- Prove2me | Theorems.Thm_Formalism_UG_P_gLoc_bc_inj
-- name    : Formalism.UG.P.gLoc_bc_inj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:31:51.28034+00:00
-- url     : https://prove2.me/theorems/bb0b3a49-88bc-4e7e-adc1-ba7c17183529
-- title:
--   P: g Loc bc inj
-- statement:
--   The P construction uses the g Loc bc inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LocalAlgebraInertPrime.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LocalAlgebraInertPrime.lean#L26-L30

import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime
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
open Formalism.UG
variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.gLoc_bc_inj (e : A ≃+* L) : Function.Injective (bc (n := n) (e : A →+* L)) := by sorry
