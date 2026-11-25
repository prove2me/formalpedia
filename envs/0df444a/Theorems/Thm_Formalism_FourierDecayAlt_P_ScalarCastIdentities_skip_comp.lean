-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_skip_comp
-- name    : Formalism.FourierDecayAlt.P.ScalarCastIdentities.skip_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:13:32.243369+00:00
-- url     : https://prove2.me/theorems/2ef674dc-df9a-4f8d-a91b-53a31f27613f
-- title:
--   Scalar Cast Identities: skip comp
-- statement:
--   The Scalar Cast Identities construction uses the skip comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L327-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L327-L333

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScalarCastIdentities
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)

theorem Formalism.FourierDecayAlt.P.ScalarCastIdentities.skip_comp (t : ℕ) (q : Fin (t + 2)) (k : Fin (t + 1)) :
    (skip1 q ∘ k.succAbove : Fin t → Fin (t + 2)) = skip2 (min (skip1 q k) q) (max (skip1 q k) q) := by sorry
