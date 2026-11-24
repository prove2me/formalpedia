-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_exists_lift
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.exists_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:43.493324+00:00
-- url     : https://prove2.me/theorems/f66ad0f2-9953-42c5-a3a3-dcfdc4a9eece
-- title:
--   BN: exists lift
-- statement:
--   The BN construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L390-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L390-L406

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

theorem Formalism.IrreducibleCountingLemmas.Z.BN.exists_lift (K : Type) [Field K] [Algebra k K] (ρ : Representation k G V)
    (τ : Representation k G W) (x : MonoidAlgebra k G) :
    ∃ y : MonoidAlgebra K G, (bc K ρ).asAlgebraHom y = (ρ.asAlgebraHom x).baseChange K ∧
      (bc K τ).asAlgebraHom y = (τ.asAlgebraHom x).baseChange K := by sorry
