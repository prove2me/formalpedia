-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_gramTw_mem
-- name    : Formalism.L2.DIV.fk_gramTw_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:12.158933+00:00
-- url     : https://prove2.me/theorems/2dbfd8eb-6fd2-4667-8481-a6e8e416a9be
-- title:
--   DIV: fk gram Tw mem
-- statement:
--   The DIV construction uses the fk gram Tw mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L153-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L153-L156

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

theorem Formalism.L2.DIV.fk_gramTw_mem {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K)
    (hG : ∀ τ a b, G τ a b ∈ K0) : gramTw lam G ∈ K0 := by sorry
