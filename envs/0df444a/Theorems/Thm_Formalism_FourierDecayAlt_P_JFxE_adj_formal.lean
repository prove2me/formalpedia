-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_adj_formal
-- name    : Formalism.FourierDecayAlt.P.JFxE.adj_formal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:56.239296+00:00
-- url     : https://prove2.me/theorems/8c665864-683b-49a4-aca3-33d34a1caf3e
-- title:
--   JFx E: adj formal
-- statement:
--   The JFx E construction uses the adj formal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L91-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L91-L111

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem Formalism.FourierDecayAlt.P.JFxE.adj_formal (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ) :
    (2 : ℂ) • (qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u + qminor E a b u) =
      ∑ σ : Equiv.Perm (Fin (m + 1)),
        ((Equiv.Perm.sign σ : ℤ) : A) * (Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i) := by sorry
