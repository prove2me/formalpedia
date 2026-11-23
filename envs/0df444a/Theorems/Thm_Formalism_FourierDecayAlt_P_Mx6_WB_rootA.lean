-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_rootA
-- name    : Formalism.FourierDecayAlt.P.Mx6.WB.rootA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:06.629534+00:00
-- url     : https://prove2.me/theorems/a641a998-393f-4d73-bcbc-49ed4b880529
-- title:
--   WB: root A
-- statement:
--   The WB construction uses the root A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L369-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L369-L386

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

theorem Formalism.FourierDecayAlt.P.Mx6.WB.rootA {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ q w N) {l : ℕ} (hl : l ∈ I)
    (hE1 : ∏ j ∈ I.erase l, (ρ j - ρ l + 1) ≠ 0)
    (hNd : Nd l * ((∏ j ∈ I.erase l, (ρ j - ρ l + 1)) * ∏ j ∈ I.erase l, (ρ j - ρ l)) = -(q.eval (-ρ l))) :
    w.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l) := by sorry
