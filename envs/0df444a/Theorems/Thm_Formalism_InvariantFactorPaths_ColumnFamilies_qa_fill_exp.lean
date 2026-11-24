-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_fill_exp
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_fill_exp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:36.119814+00:00
-- url     : https://prove2.me/theorems/769e36cd-0a70-4b11-a139-9b5eb6ffaea3
-- title:
--   Column Families: qa fill exp
-- statement:
--   The Column Families construction uses the qa fill exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L229-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean#L229-L256

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_fill_exp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) :
    qa_exp I = m := by sorry
