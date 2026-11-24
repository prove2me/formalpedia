-- Prove2me | Theorems.Thm_Formalism_HN_duality_muMax
-- name    : Formalism.HN.duality_muMax
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:25.545378+00:00
-- url     : https://prove2.me/theorems/6e60ba1d-1eaf-42b6-b48b-685d502d74a3
-- title:
--   HN: duality mu Max
-- statement:
--   The HN construction uses the duality mu Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L281-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L281-L327

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u

theorem Formalism.HN.duality_muMax (h1 : MuChar.{0, u, u}) {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (hL : L ≠ ⊥) :
    muMax (AddMonoidHom.id E) (dualZ L) = - muMin (AddMonoidHom.id E) L := by sorry
