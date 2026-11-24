-- Prove2me | Theorems.Thm_Formalism_UG_P_gLoc_level
-- name    : Formalism.UG.P.gLoc_level
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:31:50.457147+00:00
-- url     : https://prove2.me/theorems/031e7f53-78b2-4de2-a34e-d871bcb4b179
-- title:
--   P: g Loc level
-- statement:
--   The P construction uses the g Loc level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LocalAlgebraInertPrime.lean#L187-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LocalAlgebraInertPrime.lean#L187-L210

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
variable {A L : Type} [CommRing A] [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

theorem Formalism.UG.P.gLoc_level (e : A ≃+* L) (T : Subring A) (hT : ∀ x, x ∈ T ↔ e x ∈ intL L) (P : GL (Fin m) L)
    (hPO : P ∈ (bc (n := Fin m) (intL L).subtype).range) {σL : L →+* L}
    (H Lv : Subgroup (GL (Fin m) A))
    (hLv : ∀ g, g ∈ Lv ↔ g ∈ H ∧ g ∈ (bc (n := Fin m) T.subtype).range)
    (f : H ≃* GU σL m) (hf : ∀ x, ((f x : GU σL m) : GL (Fin m) L) = P⁻¹ * bc (e : A →+* L) x * P) :
    (Lv.subgroupOf H).map f.toMonoidHom = KU σL m := by sorry
