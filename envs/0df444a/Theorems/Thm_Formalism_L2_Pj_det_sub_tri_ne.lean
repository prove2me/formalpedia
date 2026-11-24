-- Prove2me | Theorems.Thm_Formalism_L2_Pj_det_sub_tri_ne
-- name    : Formalism.L2.Pj.det_sub_tri_ne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:42.261996+00:00
-- url     : https://prove2.me/theorems/2043cb16-bdb8-42c8-8d83-2a7666f34525
-- title:
--   Pj: det sub tri ne
-- statement:
--   The Pj construction uses the det sub tri ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L63-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L63-L73

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

theorem Formalism.L2.Pj.det_sub_tri_ne {i : ℕ} (h : i ≤ r) (Q : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.IsUpperTriangular)
    (hd : Q.det ≠ 0) : (Q.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0 := by sorry
