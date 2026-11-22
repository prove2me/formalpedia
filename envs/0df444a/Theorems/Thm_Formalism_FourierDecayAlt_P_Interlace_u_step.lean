-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_u_step
-- name    : Formalism.FourierDecayAlt.P.Interlace.u_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:51:20.054598+00:00
-- url     : https://prove2.me/theorems/5c5bbee6-035d-40cd-8959-2664e066fae5
-- title:
--   Interlace: u step
-- statement:
--   The Interlace construction uses the u step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Interlace.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Interlace.lean#L20-L24

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Interlace
open Finset Formalism.FourierDecayAlt.I

theorem Formalism.FourierDecayAlt.P.Interlace.u_step {k : ℕ} {u u' ρ : ℕ → ℝ} (h : Interlaces k u u' ρ) :
    ∀ i, 1 ≤ i → i + 1 ≤ k → u (i + 1) ≤ u i := by sorry
