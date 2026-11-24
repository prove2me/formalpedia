-- Prove2me | Theorems.Thm_Formalism_L2_Pj_lminor_mul_tri
-- name    : Formalism.L2.Pj.lminor_mul_tri
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:48.760806+00:00
-- url     : https://prove2.me/theorems/5009a983-993f-452f-b7e3-7e97b1bd3251
-- title:
--   Pj: lminor mul tri
-- statement:
--   The Pj construction uses the lminor mul tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L50-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L50-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem Formalism.L2.Pj.lminor_mul_tri (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ)
    (hQ : Q.IsUpperTriangular) (i : Fin (r + 1)) :
    lminor (gram τ G (P * Q)) i =
      ((Complex.normSq (Q.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
        (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det : ℝ) : ℂ) * lminor (gram τ G P) i := by sorry
