-- Prove2me | Theorems.Thm_Formalism_F_det_gram_basis_eq
-- name    : Formalism.F.det_gram_basis_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:21:43.883959+00:00
-- url     : https://prove2.me/theorems/1fa597d9-4a83-4657-acce-f2a2c81ac69a
-- title:
--   F: det gram basis eq
-- statement:
--   The F construction uses the det gram basis eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/CovolEqGram.lean#L18-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/CovolEqGram.lean#L18-L47

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F

theorem Formalism.F.det_gram_basis_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℤ L) (c : Basis κ ℤ L) :
    (Matrix.gram ℝ (fun i => (b i : E))).det = (Matrix.gram ℝ (fun k => (c k : E))).det := by sorry
