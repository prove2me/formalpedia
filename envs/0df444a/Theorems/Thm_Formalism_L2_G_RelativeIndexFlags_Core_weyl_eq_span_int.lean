-- Prove2me | Theorems.Thm_Formalism_L2_G_RelativeIndexFlags_Core_weyl_eq_span_int
-- name    : Formalism.L2.G.RelativeIndexFlags.Core.weyl_eq_span_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:34:57.475004+00:00
-- url     : https://prove2.me/theorems/5d2770e3-d5ba-4fef-b47c-cc9d68fc8080
-- title:
--   Core: weyl eq span int
-- statement:
--   The Core construction uses the weyl eq span int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/IntegralWeylLatticeSpan/WeylEqSpanInt.lean#L66-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/IntegralWeylLatticeSpan/WeylEqSpanInt.lean#L66-L79

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Lemmata_GeneralBFactLeftSide_Imports
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_IntegralWeylLatticeSpan_WeylEqSpanInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.RelativeIndexFlags Formalism.L2.G.RelativeIndexFlags.Core

theorem Formalism.L2.G.RelativeIndexFlags.Core.weyl_eq_span_int (O : Type) [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    weyl O r n hn ν = Submodule.span O ((fun f => MvPolynomial.map (Int.castRingHom O) f) ''
      (weyl ℤ r n hn ν : Set (MvPolynomial (Fin r × Fin n) ℤ))) := by sorry
