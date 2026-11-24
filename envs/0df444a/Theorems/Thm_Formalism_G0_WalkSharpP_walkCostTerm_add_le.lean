-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_walkCostTerm_add_le
-- name    : Formalism.G0.WalkSharpP.walkCostTerm_add_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:37.683309+00:00
-- url     : https://prove2.me/theorems/2dd24381-ce6c-417d-b4ec-adc6f1265cf4
-- title:
--   Walk Sharp P: walk Cost Term add le
-- statement:
--   The Walk Sharp P construction uses the walk Cost Term add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L340-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L340-L354

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

theorem Formalism.G0.WalkSharpP.walkCostTerm_add_le {V : ℕ} (a b c : Fin V → ℕ) (m c₀ : ℕ) {B : Finset (Fin V)}
    {i : Fin V → ℕ} (hi : ∀ u ∈ B, i u < m) {t : Fin V} (ht : t ∈ B) (u : Fin V) :
    accT a b c m c₀ B i u + (if u = t then c₀ else 0) ≤ a u + b u + (m - 1) * c u + m * c₀ := by sorry
