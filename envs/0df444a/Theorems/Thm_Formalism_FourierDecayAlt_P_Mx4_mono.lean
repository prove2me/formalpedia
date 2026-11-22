-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mono
-- name    : Formalism.FourierDecayAlt.P.Mx4.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:34.973961+00:00
-- url     : https://prove2.me/theorems/c14c0bba-b1ae-416b-a48b-9fbba81cf30e
-- title:
--   Mx4: mono
-- statement:
--   The Mx4 construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L267-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L267-L278

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Mx4.mono (k : ℕ) (u u' ρ : ℕ → ℝ) (h : I.Interlaces k u u' ρ) :
    ∀ d i, 1 ≤ i → i + d ≤ k → u (i + d) ≤ u i ∧ u' (i + d) ≤ u' i := by sorry
