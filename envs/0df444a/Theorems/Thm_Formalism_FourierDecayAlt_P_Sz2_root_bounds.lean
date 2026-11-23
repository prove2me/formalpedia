-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_root_bounds
-- name    : Formalism.FourierDecayAlt.P.Sz2.root_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:38.249814+00:00
-- url     : https://prove2.me/theorems/1739c3f6-07b2-415b-b1f2-cd17427d04da
-- title:
--   Sz2: root bounds
-- statement:
--   The Sz2 construction uses the root bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L233-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L233-L280

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz2.root_bounds {P Ea C0 X : ℝ} {k : ℕ} (hP0 : 0 < P) (hk1 : 1 ≤ k) (hC0 : 1 ≤ C0)
    (hX0 : 0 ≤ X) (hX8 : 8 * X ≤ k) (hEa12 : 1 / 2 ≤ Ea) (hEa2 : Ea ≤ 2)
    (hlo : Real.exp (2 * X) / C0 ≤ Ea * P ^ k) (hhi : Ea * P ^ k ≤ Real.exp (2 * X) * C0) :
    (2 * C0) ^ (-(1 / (k : ℝ))) ≤ P ∧
      P ≤ (2 * C0) ^ (1 / (k : ℝ)) * Real.exp (1 / 4) ∧
      (2 * C0) ^ (1 / (k : ℝ)) * Real.exp (1 / 4) ≤ 2 * C0 * Real.exp (1 / 4) := by sorry
