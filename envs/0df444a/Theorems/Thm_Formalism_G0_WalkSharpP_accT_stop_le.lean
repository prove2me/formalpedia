-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_accT_stop_le
-- name    : Formalism.G0.WalkSharpP.accT_stop_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:15.097481+00:00
-- url     : https://prove2.me/theorems/1f6b9495-feb3-4624-94cd-f4aee1e21d79
-- title:
--   Walk Sharp P: acc T stop le
-- statement:
--   The Walk Sharp P construction uses the acc T stop le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L356-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L356-L371

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
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
open Formalism.G0.WalkSharpP

theorem Formalism.G0.WalkSharpP.accT_stop_le {V : ℕ} (a b c : Fin V → ℕ) (m c₀ : ℕ) {B : Finset (Fin V)}
    {i : Fin V → ℕ} (hi : ∀ u ∈ B, i u < m) {v : Fin V} (hv : v ∈ B) (hiv : i v + 1 = m)
    (u : Fin V) :
    accT a b c m c₀ B i u + (if u = v then a v + c₀ else 0) ≤
      a u + b u + (m - 1) * c u + m * c₀ := by sorry
