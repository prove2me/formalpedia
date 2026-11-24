-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_g_lt
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_g_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:22.160104+00:00
-- url     : https://prove2.me/theorems/dd895466-9c8c-4154-80c4-a765d2cb7ef8
-- title:
--   Column Families: qa g lt
-- statement:
--   The Column Families construction uses the qa g lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L157-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L157-L171

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_g_lt {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (hint : Formalism.GradedWeylDivisibility.Interlaced m) (ν : Fin n → ℕ)
    (hν : Antitone ν) (hcol : ∀ t, ∑ a : Fin n, m (a, t) = ν t) (k : ℤ) (hk1 : 1 ≤ k) :
    ∀ (d : ℕ) (p p' : Fin n), p'.val = p.val + d + 1 → k ≤ ν p' → qa_g m k p < qa_g m k p' := by sorry
