-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_absH
-- name    : Formalism.FourierDecayAlt.P.Mx6.WB.absH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:30:53.02987+00:00
-- url     : https://prove2.me/theorems/e331b200-6556-4638-bd4f-4fd146692a49
-- title:
--   WB: abs H
-- statement:
--   The WB construction uses the abs H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L541-L577
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L541-L577

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

theorem Formalism.FourierDecayAlt.P.Mx6.WB.absH {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ q w N) (Qf : ℂ → ℂ)
    (hw : ∀ u, w.eval u = (∏ i ∈ I, (u + ρ i)) * Qf u + ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j))
    (u : ℂ) (h0 : ∀ i ∈ I, u + ρ i ≠ 0) (h1 : ∀ i ∈ I, u + ρ i + 1 ≠ 0) :
    q.eval u / ((∏ i ∈ I, (u + ρ i)) * ∏ i ∈ I, (u + (ρ i + 1))) =
      Qf u + ∑ l ∈ I, (N l / (u + ρ l + 1) - Nd l / (u + ρ l)) := by sorry
