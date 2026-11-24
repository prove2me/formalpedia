-- Prove2me | Theorems.Thm_Formalism_L2_Pj_linIndep_alg_pts
-- name    : Formalism.L2.Pj.linIndep_alg_pts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:43.630806+00:00
-- url     : https://prove2.me/theorems/215353f0-101e-4836-957f-d3d5136b59c5
-- title:
--   Pj: lin Indep alg pts
-- statement:
--   The Pj construction uses the lin Indep alg pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L57-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L57-L106

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ReadAlg
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
open MvPolynomial
variable {K : Type} [Field K]

theorem Formalism.L2.Pj.linIndep_alg_pts [CharZero K] {Kb : Type} [Field Kb] [IsAlgClosed Kb] [Algebra K Kb] [Normal K Kb] (p : TRing K) {m : ℕ} (a : Fin m → p.R)
    (ha : LinearIndependent K a) (v : Fin m → Kb)
    (h : ∀ φ : p.R →ₐ[K] Kb, ∑ i, v i * φ (a i) = 0) : v = 0 := by sorry
