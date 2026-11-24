-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_stab_iff
-- name    : Formalism.UG.P.afsplit_stab_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:33:56.076828+00:00
-- url     : https://prove2.me/theorems/c10f11ae-8818-4ecf-b3c5-8850ce8756b9
-- title:
--   P: afsplit stab iff
-- statement:
--   The P construction uses the afsplit stab iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L29-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L29-L77

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
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
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.afsplit_stab_iff (S : Subring A) (g : GL n A) :
    g ∈ stabGL (stdLat (n := n) (A := A) S) ↔
      (∀ i j, (g : Matrix n n A) i j ∈ S) ∧ (∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ S) := by sorry
