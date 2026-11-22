-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_alg_mem
-- name    : Formalism.HermitianLatticesTheory.locDual_alg_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:41.478437+00:00
-- url     : https://prove2.me/theorems/32894011-fd52-4e60-8067-b957a145e883
-- title:
--   Hermitian Lattices Theory: loc Dual alg mem
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Dual alg mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L38-L39

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem Formalism.HermitianLatticesTheory.locDual_alg_mem (r : R) : algebraMap R K r ∈ (1 : Submodule R K) := by sorry
