-- Prove2me | Theorems.Thm_Formalism_REAL_pfil_finite_dimensional
-- name    : Formalism.REAL.pfil_finite_dimensional
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:42.83889+00:00
-- url     : https://prove2.me/theorems/b8a557c0-6dc9-4166-af7a-9c56722fb923
-- title:
--   REAL: pfil finite dimensional
-- statement:
--   The REAL construction uses the pfil finite dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L186-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L186-L192

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
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)

theorem Formalism.REAL.pfil_finite_dimensional (h0 : FiniteDimensional ℂ (kSpan ε E u)) (j : ℕ) :
    FiniteDimensional ℂ (pfil ε E u j) := by sorry
