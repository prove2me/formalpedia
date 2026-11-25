-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_NcX_LT_GLP_glPair
-- name    : Formalism.L2.SG.Pf.NcX.LT.GLP.glPair
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:05:47.818796+00:00
-- url     : https://prove2.me/theorems/67388da0-3f22-4867-bc83-49002340d800
-- title:
--   GLP: gl Pair
-- statement:
--   The GLP construction uses the gl Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcXGLP.lean#L177-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcXGLP.lean#L177-L193

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NcXGLP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcX Formalism.L2.SG.Pf.NcX.LT Formalism.L2.SG.Pf.NcX.LT.GLP
variable {K : Type*} [Field K]

theorem Formalism.L2.SG.Pf.NcX.LT.GLP.glPair {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (ξ η : Fin a → Module.Dual K V) (hx : LinearIndependent K x)
    (hy : LinearIndependent K y) (hξ : LinearIndependent K ξ) (hη : LinearIndependent K η)
    (h : ∀ i j, ξ i (x j) = η i (y j)) :
    ∃ A : V ≃ₗ[K] V, (∀ j, A (x j) = y j) ∧ ∀ i v, η i (A v) = ξ i v := by sorry
