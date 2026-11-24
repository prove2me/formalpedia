-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_decomp
-- name    : Formalism.InvariantFactorPaths.KP.LL.decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:03.23103+00:00
-- url     : https://prove2.me/theorems/5a18d2a5-69ad-4982-acfd-316912a8ab4c
-- title:
--   LL: decomp
-- statement:
--   The LL construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/TieFPowMulFree.lean#L247-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/TieFPowMulFree.lean#L247-L310

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ScalSum
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree
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
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)

theorem Formalism.InvariantFactorPaths.KP.LL.decomp [CharZero k] (hr : 1 ≤ r) (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (o n z : ℕ) (x : MvPolynomial σ k)
    (hv : ∀ m, min o n < m → (tieF w e ^ m) x = 0) :
    X zv ^ z * x = ∑ l ∈ range (min o n + 1), ehP w e zv sv ^ l *
      M.tieP w e zv sv (o - l) (n - l) z
        (((((l.factorial : k)) ^ 2 * ((o + n + r + z - l).choose l : k)))⁻¹ • (tieF w e ^ l) x) := by sorry
