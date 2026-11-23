-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_weighted_sum_difference_identity
-- name    : Formalism.FourierDecayAlt.P.Mx6.WB.weighted_sum_difference_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:16:47.841978+00:00
-- url     : https://prove2.me/theorems/2ffd7181-b54c-4caa-9b36-e76189cdf6a4
-- title:
--   WB: weighted sum difference identity
-- statement:
--   The WB construction uses the weighted sum difference identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L579-L598
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L579-L598

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

theorem Formalism.FourierDecayAlt.P.Mx6.WB.weighted_sum_difference_identity {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ q w N) (c s c0 : ℂ)
    (hw : ∀ u, w.eval u = (∏ i ∈ I, (u + ρ i)) * (c * (u ^ 2 + s * u) + c0) +
      ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j))
    (u v : ℂ) (h0 : ∀ i ∈ I, u + ρ i ≠ 0) (h1 : ∀ i ∈ I, u + ρ i + 1 ≠ 0)
    (k0 : ∀ i ∈ I, v + ρ i ≠ 0) (k1 : ∀ i ∈ I, v + ρ i + 1 ≠ 0) :
    (u - v) * ((u + v + s) * (-c) + ∑ j ∈ I, (N j / ((u + ρ j + 1) * (v + ρ j + 1)) - Nd j / ((u + ρ j) * (v + ρ j)))) =
      q.eval v / ((∏ i ∈ I, (v + ρ i)) * ∏ i ∈ I, (v + (ρ i + 1))) -
      q.eval u / ((∏ i ∈ I, (u + ρ i)) * ∏ i ∈ I, (u + (ρ i + 1))) := by sorry
