-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_fin_succ
-- name    : Formalism.InvariantFactorPaths.G7.CSym.eF_fin_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:52.257799+00:00
-- url     : https://prove2.me/theorems/896fe80d-851d-4de3-afa0-fdf5d719cb4c
-- title:
--   CSym: e F fin succ
-- statement:
--   The CSym construction uses the e F fin succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L62-L72

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.CSym
variable {K σ : Type} [CommRing K] [Fintype σ]

theorem Formalism.InvariantFactorPaths.G7.CSym.eF_fin_succ {g : ℕ} (x : Fin (g + 1) → K) (l : ℕ) :
    eF x (l + 1) = eF (fun i : Fin g => x i.castSucc) (l + 1) +
      x (Fin.last g) * eF (fun i : Fin g => x i.castSucc) l := by sorry
