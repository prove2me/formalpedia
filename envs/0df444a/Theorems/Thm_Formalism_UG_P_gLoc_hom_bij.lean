-- Prove2me | Theorems.Thm_Formalism_UG_P_gLoc_hom_bij
-- name    : Formalism.UG.P.gLoc_hom_bij
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:31:52.168831+00:00
-- url     : https://prove2.me/theorems/3dbefa84-9cba-4c68-8854-24920770c5d2
-- title:
--   P: g Loc hom bij
-- statement:
--   The P construction uses the g Loc hom bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LocalAlgebraInertPrime.lean#L165-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LocalAlgebraInertPrime.lean#L165-L185

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

theorem Formalism.UG.P.gLoc_hom_bij (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (P : GL (Fin m) L)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A)) :
    Function.Bijective (gLoc_hom σA σL e he P hP H hH) := by sorry
