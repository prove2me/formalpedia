-- Prove2me | Theorems.Thm_Formalism_UG_P_glint_exists_denom
-- name    : Formalism.UG.P.glint_exists_denom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:27:14.342721+00:00
-- url     : https://prove2.me/theorems/3a886ed4-248c-4113-97b5-de945f08ec06
-- title:
--   P: glint exists denom
-- statement:
--   The P construction uses the glint exists denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/GlintPrincRelIndexNeZero.lean#L114-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/GlintPrincRelIndexNeZero.lean#L114-L140

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.glint_exists_denom (A : ValuationSubring L) (g : GL n L) :
    ∃ c : A.toSubring, c ≠ 0 ∧
      (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) A.toSubring.subtype).range ∧
      (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈
        (RingHom.mapMatrix (m := n) A.toSubring.subtype).range := by sorry
