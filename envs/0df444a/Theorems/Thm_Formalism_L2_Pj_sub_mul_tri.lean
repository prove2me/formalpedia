-- Prove2me | Theorems.Thm_Formalism_L2_Pj_sub_mul_tri
-- name    : Formalism.L2.Pj.sub_mul_tri
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:54.206605+00:00
-- url     : https://prove2.me/theorems/dcfe0a77-b205-4bac-8e53-db0452bd76a3
-- title:
--   Pj: sub mul tri
-- statement:
--   The Pj construction uses the sub mul tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L32-L48

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

theorem Formalism.L2.Pj.sub_mul_tri {i : ℕ} (h : i ≤ r) (Q A : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.IsUpperTriangular) :
    (Qᵀ * A * Q.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      (Q.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ * A.submatrix (Fin.castLE h) (Fin.castLE h) *
        (Q.submatrix (Fin.castLE h) (Fin.castLE h)).map (starRingEnd ℂ) := by sorry
