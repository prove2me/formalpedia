-- Prove2me | Theorems.Thm_Formalism_UG_P_map_polyAct_pow
-- name    : Formalism.UG.P.map_polyAct_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:20.069513+00:00
-- url     : https://prove2.me/theorems/b0e4514f-5f8b-4ca9-b42f-c6d927a5eef0
-- title:
--   P: map poly Act pow
-- statement:
--   The P construction uses the map poly Act pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LinSubstIsHomogeneous.lean#L68-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LinSubstIsHomogeneous.lean#L68-L80

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.map_polyAct_pow (g : GL n O) (K : ℕ) :
    map (polyAct O n g).toRingHom
        ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K)
      = (∑ i, C (X i) *
          map C (∑ j, C (((g⁻¹ : GL n O) : Matrix n n O) j i) * X j) :
            MvPolynomial n (MvPolynomial n O)) ^ K := by sorry
