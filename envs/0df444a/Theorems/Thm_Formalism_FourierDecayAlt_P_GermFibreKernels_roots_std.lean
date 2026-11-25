-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermFibreKernels_roots_std
-- name    : Formalism.FourierDecayAlt.P.GermFibreKernels.roots_std
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:26:49.666919+00:00
-- url     : https://prove2.me/theorems/25e04ea5-19f6-5db6-bafe-ab6285defb47
-- title:
--   Germ Fibre Kernels: roots std
-- statement:
--   The Germ Fibre Kernels construction uses the roots std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ToStdAppend.lean#L32-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ToStdAppend.lean#L32-L67

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNegBetaL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ToStdAppend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermFibreKernels
open Formalism.FourierDecayAlt NumberField
noncomputable section

theorem Formalism.FourierDecayAlt.P.GermFibreKernels.roots_std (r : ℕ) (g : ℝ) (hg : 0 < g) (b s : ℕ) (hs : 2 ≤ s) (t c z : ℂ) :
    fs r g b s z ^ s = (-1) ^ (s + 1) * (fs r g (b + (s - 1)) 1 c * fs r g b (s - 1) t ^ (s - 1)) ↔
      z ^ s = c * t ^ (s - 1) := by sorry
