-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_harmonicProjection_expand
-- name    : Formalism.InvariantFactorPaths.KP.LL.harmonicProjection_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:58:19.376054+00:00
-- url     : https://prove2.me/theorems/4a08c694-b1ba-41ce-8212-9532d4909fc9
-- title:
--   LL: harmonic Projection expand
-- statement:
--   The LL construction uses the harmonic Projection expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/TieFPowMulFree.lean#L53-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/TieFPowMulFree.lean#L53-L66

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

theorem Formalism.InvariantFactorPaths.KP.LL.harmonicProjection_expand (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (o n z : ℕ) (x : MvPolynomial σ k) :
    M.tieP w e zv sv o n z x = ∑ m ∈ range (o + 1),
      (((-1 : k) ^ m) / (((m.factorial : k) ^ 2) * ((o + n + r + z - 1).choose m : k))) •
        (ehP w e zv sv ^ m * (X zv ^ z * (tieF w e ^ m) x)) := by sorry
