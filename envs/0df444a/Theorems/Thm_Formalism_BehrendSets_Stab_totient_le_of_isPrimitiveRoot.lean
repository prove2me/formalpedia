-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Stab_totient_le_of_isPrimitiveRoot
-- name    : Formalism.BehrendSets.Stab.totient_le_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:12.961368+00:00
-- url     : https://prove2.me/theorems/f72bceea-e97b-4050-a8ca-dc3258ffe753
-- title:
--   Stab: totient le of is Primitive Root
-- statement:
--   The Stab construction uses the totient le of is Primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TotientLeOfIsPrimitiveRoot.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TotientLeOfIsPrimitiveRoot.lean#L7-L16

import Definitions.Def_Formalism_BehrendSets_StatementE
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TotientLeOfIsPrimitiveRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Module Matrix
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Stab

theorem Formalism.BehrendSets.Stab.totient_le_of_isPrimitiveRoot {E K : Type} [Field E] [NumberField E] [Field K] [Algebra E K]
    [FiniteDimensional E K] {g : ℕ} (hg : 0 < g) {ζ : K} (hζ : IsPrimitiveRoot ζ g) :
    Nat.totient g ≤ finrank ℚ E * finrank E K := by sorry
