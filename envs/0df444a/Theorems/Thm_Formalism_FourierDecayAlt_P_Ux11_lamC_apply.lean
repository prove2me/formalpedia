-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_lamC_apply
-- name    : Formalism.FourierDecayAlt.P.Ux11.lamC_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:24.293587+00:00
-- url     : https://prove2.me/theorems/4561a815-3e38-4f01-a0cd-2ce71fa13fb4
-- title:
--   Ux11: lam C apply
-- statement:
--   The Ux11 construction uses the lam C apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L322-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L322-L323

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {k ρ mm : ℕ} {E V : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V]
  [NormedSpace ℂ V] {a : ℝ} {S : Set (B.Mat k ρ)}

theorem Formalism.FourierDecayAlt.P.Ux11.lamC_apply (M : U.CCModel k ρ E a mm S V) (t : Idx k ρ mm) (w : V) :
    lamC M t w = ((B.gN t.1.2.2 ^ a : ℝ) : ℂ) • B.dLR t.1.1 t.1.2.1 (M.ev w) t.1.2.2 := by sorry
