-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGram_sub
-- name    : Formalism.FourierDecayAlt.P.BaseGramNonnegativity.baseGram_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:32.594559+00:00
-- url     : https://prove2.me/theorems/543340e8-d4c1-485e-b3e2-1b65ba1757bb
-- title:
--   Base Gram Nonnegativity: base Gram sub
-- statement:
--   The Base Gram Nonnegativity construction uses the base Gram sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockEstimatesSumForm.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockEstimatesSumForm.lean#L23-L25

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BaseGramNonnegativity
open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB
variable {E W : Type} [Field E] (D : Data E W)

theorem Formalism.FourierDecayAlt.P.BaseGramNonnegativity.baseGram_sub (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) (κ κ' : Pt E → Pt E → ℂ) :
    D.N0 ε k w Y (fun h h' => κ' h h' - κ h h') = D.N0 ε k w Y κ' - D.N0 ε k w Y κ := by sorry
