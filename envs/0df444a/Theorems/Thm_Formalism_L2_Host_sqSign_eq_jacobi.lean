-- Prove2me | Theorems.Thm_Formalism_L2_Host_sqSign_eq_jacobi
-- name    : Formalism.L2.Host.sqSign_eq_jacobi
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:56:16.626257+00:00
-- url     : https://prove2.me/theorems/edd220ca-a4d8-48d7-96d0-9dcf0dccbe58
-- title:
--   Host: sq Sign eq jacobi
-- statement:
--   The Host construction uses the sq Sign eq jacobi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/ArtGCut.lean#L9-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/ArtGCut.lean#L9-L48

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_ArtGCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.Host

theorem Formalism.L2.Host.sqSign_eq_jacobi {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hq4 : q % 4 = 3) (hp2 : p ≠ 2)
    (v : (ZMod q)ˣ) (hv : (v : ZMod q) = (p : ZMod q)) :
    ((sqSign v : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p := by sorry
