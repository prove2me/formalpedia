-- Prove2me | Theorems.Thm_Formalism_G0_ManyOrbitsP_esymmR_le
-- name    : Formalism.G0.ManyOrbitsP.esymmR_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:10.666371+00:00
-- url     : https://prove2.me/theorems/cebb2826-dcb6-4c3f-8748-a13a929cf494
-- title:
--   Many Orbits P: esymm R le
-- statement:
--   The Many Orbits P construction uses the esymm R le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L58-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L58-L75

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.ManyOrbitsP

theorem Formalism.G0.ManyOrbitsP.esymmR_le {V : ℕ} (κ : Fin V → ℝ) (hκ : ∀ v, 0 ≤ κ v) (m : ℝ) (hm : 0 ≤ m) (k : ℕ) :
    m ^ k * esymmR κ k ≤ (m * ∑ v, κ v) ^ k / k.factorial := by sorry
