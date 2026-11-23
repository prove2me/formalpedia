-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_CmData_stdData_cm
-- name    : Formalism.L2.Th1.H.CmData.stdData_cm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:25.526802+00:00
-- url     : https://prove2.me/theorems/64153ea9-28de-4b58-99a6-b4f7875fa9cf
-- title:
--   Cm Data: std Data cm
-- statement:
--   The Cm Data construction uses the std Data cm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/StdDataCmProof.lean#L93-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/StdDataCmProof.lean#L93-L123

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_StdDataCmProof
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H Formalism.L2.Th1.H.CmData
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmPair cmTheta)
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.L2.Th1.H.CmData.stdData_cm (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (h4 : 4 * (a : ℤ) * c = b ^ 2 + d)
    (hodd : Odd a) (h8 : d % 8 = 7) (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hg : IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
      (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    (hsd : IsSelfDual (matH h) Λ) (hst : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ)
    (i1 : relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0)
    (i2 : relIdx (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
      (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n)) ≠ 0) :
    StdData (cmL a b d ha hd lam hlam) (lam * a) h Λ (alphaQ (Real.sqrt d / 2) (matH h))
      (alphaQ (Real.sqrt d / 2) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))) g := by sorry
