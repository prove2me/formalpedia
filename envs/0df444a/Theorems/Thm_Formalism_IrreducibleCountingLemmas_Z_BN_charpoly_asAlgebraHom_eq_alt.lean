-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_charpoly_asAlgebraHom_eq_alt
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.charpoly_asAlgebraHom_eq_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:31.92866+00:00
-- url     : https://prove2.me/theorems/2478a208-4724-4e31-b7fb-262e16e043be
-- title:
--   BN: charpoly as Algebra Hom eq alt
-- statement:
--   The BN construction uses the charpoly as Algebra Hom eq alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L425-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L425-L438

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

theorem Formalism.IrreducibleCountingLemmas.Z.BN.charpoly_asAlgebraHom_eq_alt [FiniteDimensional k V] [FiniteDimensional k W]
    (K : Type) [Field K] [Algebra k K] [IsAlgClosed K]
    (ρ : Representation k G V) (τ : Representation k G W)
    (h : ∀ g, (ρ g).charpoly = (τ g).charpoly) (x : MonoidAlgebra k G) :
    (ρ.asAlgebraHom x).charpoly = (τ.asAlgebraHom x).charpoly := by sorry
