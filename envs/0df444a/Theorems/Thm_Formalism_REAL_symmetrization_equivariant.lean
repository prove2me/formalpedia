-- Prove2me | Theorems.Thm_Formalism_REAL_symmetrization_equivariant
-- name    : Formalism.REAL.symmetrization_equivariant
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:54.416101+00:00
-- url     : https://prove2.me/theorems/a5addaae-ab7d-4f4c-a57b-addd31161cd1
-- title:
--   REAL: symmetrization equivariant
-- statement:
--   The REAL construction uses the symmetrization equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L512-L543
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L512-L543

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.symmetrization_equivariant (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {j : ℕ} (c d : Fin n)
    (F : Arr V n j) : thetaA E j (arrE E j c d F) = E c d (thetaA E j F) := by sorry
