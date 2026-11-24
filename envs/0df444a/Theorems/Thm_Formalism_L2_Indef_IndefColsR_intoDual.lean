-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefColsR_intoDual
-- name    : Formalism.L2.Indef.IndefColsR.intoDual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:14.069934+00:00
-- url     : https://prove2.me/theorems/f892b8a5-47d9-437e-872b-fcde2d336216
-- title:
--   Indef Cols R: into Dual
-- statement:
--   The Indef Cols R construction uses the into Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L393-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L393-L408

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_IndefCols_intoDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Indef.IndefColsR
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
  (S : IndefColsR Df Dc Sp N)

theorem Formalism.L2.Indef.IndefColsR.intoDual (hD : DivIntoDualShift) (hG : LatticeGlue) (wf : Df.WF) (u : Dc.Mem)
    (Nu Nu' : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (σ : HeightOneSpectrum (𝓞 K) → ℝ)
    (τ : HeightOneSpectrum (𝓞 K) → ℤ)
    (hL2 : ∀ w, ∀ φ ∈ Nu, ∀ F ∈ Df.Mt (S.μ w),
      Dc.Pt u (S.μ w) φ F = 0 ∨ σ w ≤ (vw w (Dc.Pt u (S.μ w) φ F) : ℝ))
    (hτ : ∀ w, τ w ≤ ⌈σ w⌉) (hsh : IsShift Nu Nu' τ) :
    ∀ φ ∈ Nu', S.col.B u φ ∈ Formalism.HN.dualLat S.RR := by sorry
