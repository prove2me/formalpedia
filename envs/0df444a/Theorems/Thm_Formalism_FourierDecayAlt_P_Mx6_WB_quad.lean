-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_quad
-- name    : Formalism.FourierDecayAlt.P.Mx6.WB.quad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:02.12368+00:00
-- url     : https://prove2.me/theorems/6196eda8-28c6-4c43-aabc-6084c15f7341
-- title:
--   WB: quad
-- statement:
--   The WB construction uses the quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L462-L539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L462-L539

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

theorem Formalism.FourierDecayAlt.P.Mx6.WB.quad {I : Finset ℕ} {ρ : ℕ → ℂ} (hinj : ∀ i ∈ I, ∀ j ∈ I, ρ i = ρ j → i = j) {q1 w : ℂ[X]} (hq1 : q1.Monic)
    (hdeg : q1.natDegree = 2 * I.card + 2) {c : ℂ} (hc : c ≠ 0) {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ (C c * q1) w N)
    (hroot : ∀ l ∈ I, w.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l)) :
    ∃ c0 : ℂ, ∀ u : ℂ, w.eval u = (∏ i ∈ I, (u + ρ i)) *
      (c * (u ^ 2 + (q1.nextCoeff - ∑ i ∈ I, (ρ i + 1) - ∑ i ∈ I, ρ i) * u) + c0) +
      ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j) := by sorry
