-- Prove2me | Theorems.Thm_Formalism_L2_G_RelativeIndexFlags_Core_map_rowAct
-- name    : Formalism.L2.G.RelativeIndexFlags.Core.map_rowAct
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:36.257783+00:00
-- url     : https://prove2.me/theorems/a57c9432-6087-4e8c-aa26-39dda3b81c2c
-- title:
--   Core: map row Act
-- statement:
--   The Core construction uses the map row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/IntegralWeylLatticeSpan/WeylEqSpanInt.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/IntegralWeylLatticeSpan/WeylEqSpanInt.lean#L17-L27

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

theorem Formalism.L2.G.RelativeIndexFlags.Core.map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (F : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (rowAct R g F) = rowAct S (g.map φ) (MvPolynomial.map φ F) := by sorry
