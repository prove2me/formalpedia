-- Prove2me | Theorems.Thm_Formalism_GM_DetBound_coeff_le_gaussR
-- name    : Formalism.GM.DetBound.coeff_le_gaussR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:21.355426+00:00
-- url     : https://prove2.me/theorems/cea7c207-8397-4ca9-b82f-f750a58a4063
-- title:
--   Det Bound: coeff le gauss R
-- statement:
--   The Det Bound construction uses the coeff le gauss R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L22-L23

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DetBound
open Finset Polynomial
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.GM.DetBound.coeff_le_gaussR (ρ : NNReal) (P : K[X]) (k : ℕ) : ‖P.coeff k‖₊ * ρ ^ k ≤ gaussR ρ P := by sorry
