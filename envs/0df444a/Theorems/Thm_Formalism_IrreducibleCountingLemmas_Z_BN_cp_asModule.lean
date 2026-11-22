-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_asModule
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.cp_asModule
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:16.397748+00:00
-- url     : https://prove2.me/theorems/855b13d1-f4bb-41b3-9a5b-c82961ee20e5
-- title:
--   BN: cp as Module
-- statement:
--   The BN construction uses the cp as Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L408-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L408-L411

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
open TensorProduct
variable {k G V W : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

theorem Formalism.IrreducibleCountingLemmas.Z.BN.cp_asModule [FiniteDimensional k V] (ρ : Representation k G V) (x : MonoidAlgebra k G) :
    cp k ρ.asModule x = (ρ.asAlgebraHom x).charpoly := by sorry
