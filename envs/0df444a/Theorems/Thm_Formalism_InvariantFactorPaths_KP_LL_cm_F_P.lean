-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_F_P
-- name    : Formalism.InvariantFactorPaths.KP.LL.cm_F_P
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:17.489248+00:00
-- url     : https://prove2.me/theorems/801aed5c-4278-484c-983b-f5b5b22bfc3b
-- title:
--   LL: cm F P
-- statement:
--   The LL construction uses the cm F P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeLinearHolds.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeLinearHolds.lean#L37-L47

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}

theorem Formalism.InvariantFactorPaths.KP.LL.cm_F_P {r' : ℕ} (w' e' : Fin r' → σ) (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ)
    (hw : ∀ c, zv ≠ w' c ∧ sv ≠ w' c ∧ (∀ d, w d ≠ w' c) ∧ ∀ d, e d ≠ w' c)
    (he : ∀ c, zv ≠ e' c ∧ sv ≠ e' c ∧ (∀ d, w d ≠ e' c) ∧ ∀ d, e d ≠ e' c) :
    Commute (tieF (k := ℚ_[p]) w' e') (cmTiePL w e zv sv o n z) := by sorry
