-- Prove2me | Theorems.Thm_Formalism_UG_P_wlocal_good_mul
-- name    : Formalism.UG.P.wlocal_good_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:47.722468+00:00
-- url     : https://prove2.me/theorems/825de91c-3c51-48be-9561-47d4c56d3584
-- title:
--   P: wlocal good mul
-- statement:
--   The P construction uses the wlocal good mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L83-L87

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]

theorem Formalism.UG.P.wlocal_good_mul {r n : ℕ} {hn : n ≤ r} {ν : Fin n → ℕ} {A B : Matrix (Fin r) (Fin r) R}
    (hA : wlocal_Good hn ν A) (hB : wlocal_Good hn ν B) : wlocal_Good hn ν (A * B) := by sorry
