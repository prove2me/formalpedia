-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_sign_core
-- name    : Formalism.FourierDecayAlt.P.Interlace.sign_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:53.462775+00:00
-- url     : https://prove2.me/theorems/c23d3a76-c131-43b6-8ae9-318f58bb761b
-- title:
--   Interlace: sign core
-- statement:
--   The Interlace construction uses the sign core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Interlace.lean#L26-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Interlace.lean#L26-L49

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

theorem Formalism.FourierDecayAlt.P.Interlace.sign_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) (e : ℝ)
    (he : -1 ≤ e ∧ e ≤ 1) :
    0 < (-1 : ℝ) ^ (k - l) * xpoly k ρ (Y + e) := by sorry
