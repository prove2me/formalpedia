-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_C_mem
-- name    : Formalism.L2.DIV.fk_C_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:55.947794+00:00
-- url     : https://prove2.me/theorems/8838f2e4-5318-4133-ad7a-bb187e4d958d
-- title:
--   DIV: fk C mem
-- statement:
--   The DIV construction uses the fk C mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L111-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L111-L112

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] (K0 : Subfield K)

theorem Formalism.L2.DIV.fk_C_mem {σ : Type} {a : K} (ha : a ∈ K0) : (C a : MvPolynomial σ K) ∈ (map (σ := σ) K0.subtype).range := by sorry
