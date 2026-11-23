-- Prove2me | Theorems.Thm_Formalism_L2_Pj_eq_zero_of_pts
-- name    : Formalism.L2.Pj.eq_zero_of_pts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:19.641408+00:00
-- url     : https://prove2.me/theorems/a41a880b-083f-4d32-af18-871ff7fe2813
-- title:
--   Pj: eq zero of pts
-- statement:
--   The Pj construction uses the eq zero of pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L13-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L13-L44

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

theorem Formalism.L2.Pj.eq_zero_of_pts {M : Type} [Field M] [IsAlgClosed M] [Algebra K M] (p : TRing K) (a : p.R)
    (h : ∀ ψ : p.R →ₐ[K] M, ψ a = 0) : a = 0 := by sorry
