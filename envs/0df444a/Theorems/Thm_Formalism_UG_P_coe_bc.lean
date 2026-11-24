-- Prove2me | Theorems.Thm_Formalism_UG_P_coe_bc
-- name    : Formalism.UG.P.coe_bc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:51.787119+00:00
-- url     : https://prove2.me/theorems/7c5712be-ddd5-4ec6-a95a-c2791bbc4203
-- title:
--   P: coe bc
-- statement:
--   The P construction uses the coe bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabstd.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabstd.lean#L41-L43

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Matrix
variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.coe_bc (φ : R →+* A) (u : GL n R) :
    ((bc (n := n) φ u : GL n A) : Matrix n n A) = (u : Matrix n n R).map φ := by sorry
