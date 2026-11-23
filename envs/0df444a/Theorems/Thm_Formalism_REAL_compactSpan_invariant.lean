-- Prove2me | Theorems.Thm_Formalism_REAL_compactSpan_invariant
-- name    : Formalism.REAL.compactSpan_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:20.96596+00:00
-- url     : https://prove2.me/theorems/67e96250-21fb-4dfb-a909-3699876c47b2
-- title:
--   REAL: compact Span invariant
-- statement:
--   The REAL construction uses the compact Span invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L191-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L191-L196

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem Formalism.REAL.compactSpan_invariant (ε : Fin n → Bool) (T : Fin n → Fin n → Module.End ℂ V) (x : V) :
    KStable ε T (kSpan ε T x) := by sorry
