-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pst_scal_mem
-- name    : Formalism.InvariantFactorPaths.KP.LL.pst_scal_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:41.460456+00:00
-- url     : https://prove2.me/theorems/2af82aeb-b861-43a0-ae45-aec9ce03249e
-- title:
--   LL: pst scal mem
-- statement:
--   The LL construction uses the pst scal mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PstScalMem.lean#L17-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PstScalMem.lean#L17-L45

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PstScalMem
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

theorem Formalism.InvariantFactorPaths.KP.LL.pst_scal_mem {p : ℕ} [Fact p.Prime] {σ : Type} (Λ : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (a u m j k : ℕ) (hk : k ≤ j) (hu : a + Nat.log p j ≤ u) (s : ℚ_[p]) (hs : ‖s‖ ≤ 1)
    (y : MvPolynomial σ ℚ_[p])
    (hy : (((p : ℚ_[p]) ^ a * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • y) ∈ Λ) :
    ((s * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) * ((j.choose k : ℕ) : ℚ_[p]))⁻¹) • y) ∈ Λ := by sorry
