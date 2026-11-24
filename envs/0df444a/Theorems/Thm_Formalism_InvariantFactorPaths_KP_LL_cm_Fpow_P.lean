-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_Fpow_P
-- name    : Formalism.InvariantFactorPaths.KP.LL.cm_Fpow_P
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:57.59022+00:00
-- url     : https://prove2.me/theorems/645ffbcc-d6fd-45c6-bd15-e7509ca7ff87
-- title:
--   LL: cm Fpow P
-- statement:
--   The LL construction uses the cm Fpow P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeLinearHolds.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeLinearHolds.lean#L49-L56

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

theorem Formalism.InvariantFactorPaths.KP.LL.cm_Fpow_P {r' : ℕ} (w' e' : Fin r' → σ) (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ)
    (hw : ∀ c, zv ≠ w' c ∧ sv ≠ w' c ∧ (∀ d, w d ≠ w' c) ∧ ∀ d, e d ≠ w' c)
    (he : ∀ c, zv ≠ e' c ∧ sv ≠ e' c ∧ (∀ d, w d ≠ e' c) ∧ ∀ d, e d ≠ e' c) (m : ℕ)
    (x : MvPolynomial σ ℚ_[p]) :
    (tieF w' e' ^ m) (tieP w e zv sv o n z x) = tieP w e zv sv o n z ((tieF w' e' ^ m) x) := by sorry
