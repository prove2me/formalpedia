-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_indep_tw
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_indep_tw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:16.663128+00:00
-- url     : https://prove2.me/theorems/33531dad-0d43-4c22-ab43-08e4ac98c339
-- title:
--   Column Families: qc indep tw
-- statement:
--   The Column Families construction uses the qc indep tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L107-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L107-L131

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_indep_tw {K : Type} [CommRing K] {M : GLMod n} (CF : ColFam M) {ι' : Type} (e : ι' ≃ M.ι) (ε : ℤ)
    (h : ∀ nu : Fin n → ℤ, LinearIndependent K
      (fun j : {j : CF.J // CF.mu j = nu} => fun i => ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : K)))
    (nu : Fin n → ℤ) : LinearIndependent K
      (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => fun i' : ι' =>
        ((CF.ph j.1 (e i') (qc_idxE (CF.mu j.1) ε (canT (qc_sh (CF.mu j.1) ε))) : ℤ) : K)) := by sorry
