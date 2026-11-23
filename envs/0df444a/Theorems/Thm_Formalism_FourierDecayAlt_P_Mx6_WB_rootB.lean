-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_rootB
-- name    : Formalism.FourierDecayAlt.P.Mx6.WB.rootB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:07.997559+00:00
-- url     : https://prove2.me/theorems/7d6657ce-2542-4612-8056-fa78e5074fbb
-- title:
--   WB: root B
-- statement:
--   The WB construction uses the root B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L388-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L388-L436

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section

theorem Formalism.FourierDecayAlt.P.Mx6.WB.rootB {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (h : W1 I ρ q w N)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, ρ i = ρ j → i = j) {l j0 : ℕ} (hl : l ∈ I) (hj0 : j0 ∈ I) (hne : j0 ≠ l)
    (hρ : ρ j0 + 1 = ρ l) (hq : (X + C (ρ l)) ^ 2 ∣ q) (hN0 : N j0 = 0) :
    w.eval (-ρ l) = N l * ∏ j ∈ I.erase l, (ρ j - ρ l) := by sorry
