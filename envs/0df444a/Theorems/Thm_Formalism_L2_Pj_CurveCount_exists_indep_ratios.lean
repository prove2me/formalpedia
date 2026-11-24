-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CurveCount_exists_indep_ratios
-- name    : Formalism.L2.Pj.CurveCount.exists_indep_ratios
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:14.128799+00:00
-- url     : https://prove2.me/theorems/bf7738e5-4871-4a57-ae2f-32212273d47d
-- title:
--   Curve Count: exists indep ratios
-- statement:
--   The Curve Count construction uses the exists indep ratios property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CurveCountA.lean#L29-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CurveCountA.lean#L29-L116

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CurveCountA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CurveCount
open MvPolynomial

theorem Formalism.L2.Pj.CurveCount.exists_indep_ratios {K κ : Type*} [Field K] [Field κ] [Algebra K κ] {N D : ℕ} (x : Fin N → κ) (a : Fin N)
    (hxa : x a ≠ 0) (t : Fin (D + 1) × Fin N → κ) (ht : AlgebraicIndependent K t)
    (hlin : ∀ i : Fin D, ∑ k, t (i.succ, k) * x k = 0) (hlin0 : ∑ k, t (0, k) * x k = 1) :
    ∃ s : Finset κ, s.card = D ∧ (↑s : Set κ) ⊆ Set.range (fun i => x i / x a) ∧
      AlgebraicIndepOn K id (↑s : Set κ) := by sorry
