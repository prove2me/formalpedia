-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_bc_of
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.cp_bc_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:06.551959+00:00
-- url     : https://prove2.me/theorems/f2e7eaa6-133e-4cb5-afb4-70dd9d829124
-- title:
--   BN: cp bc of
-- statement:
--   The BN construction uses the cp bc of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L413-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L413-L417

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

theorem Formalism.IrreducibleCountingLemmas.Z.BN.cp_bc_of [FiniteDimensional k V] (K : Type) [Field K] [Algebra k K]
    (ρ : Representation k G V) (g : G) :
    cp K (bc K ρ).asModule (MonoidAlgebra.of K G g) = (ρ g).charpoly.map (algebraMap k K) := by sorry
