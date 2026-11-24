-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_gauss
-- name    : Formalism.HermitianLatticesTheory.thetaSummable_gauss
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:22.446135+00:00
-- url     : https://prove2.me/theorems/bcd8a70f-5662-4c53-b2fa-012ac81d9ac8
-- title:
--   Hermitian Lattices Theory: theta Summable gauss
-- statement:
--   The Hermitian Lattices Theory construction uses the theta Summable gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L11-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L11-L32

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory

theorem Formalism.HermitianLatticesTheory.thetaSummable_gauss {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℤ => Real.exp (-δ * (n : ℝ) ^ 2)) := by sorry
