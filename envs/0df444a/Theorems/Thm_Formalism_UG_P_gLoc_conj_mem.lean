-- Prove2me | Theorems.Thm_Formalism_UG_P_gLoc_conj_mem
-- name    : Formalism.UG.P.gLoc_conj_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:31:52.038847+00:00
-- url     : https://prove2.me/theorems/cdca6349-54da-4771-bc39-631874a9bc40
-- title:
--   P: g Loc conj mem
-- statement:
--   The P construction uses the g Loc conj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LocalAlgebraInertPrime.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LocalAlgebraInertPrime.lean#L124-L131

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

theorem Formalism.UG.P.gLoc_conj_mem {G : Type} [Group G] (K : Subgroup G) (P : G) (hP : P ∈ K) (g : G) :
    g ∈ K ↔ P⁻¹ * g * P ∈ K := by sorry
