-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_herm_mulVec
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.herm_mulVec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:56:28.910568+00:00
-- url     : https://prove2.me/theorems/924fe410-8f06-4057-940d-0fed5d23bd51
-- title:
--   Hermitian Projections: herm mul Vec
-- statement:
--   The Hermitian Projections construction uses the herm mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L149-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L149-L154

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
variable {n : Type*} [Fintype n]

theorem Formalism.FourierDecayAlt.P.HermitianProjections.herm_mulVec {m ι κ : Type*} [Fintype m] [Fintype ι] [Fintype κ] (H : Matrix m m ℂ)
    (A : Matrix m ι ℂ) (B : Matrix m κ ℂ) (a : ι → ℂ) (b : κ → ℂ) :
    herm H (A *ᵥ a) (B *ᵥ b) = star b ⬝ᵥ ((Bᴴ * H * A) *ᵥ a) := by sorry
