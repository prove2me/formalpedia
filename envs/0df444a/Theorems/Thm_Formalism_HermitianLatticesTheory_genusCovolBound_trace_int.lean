-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_trace_int
-- name    : Formalism.HermitianLatticesTheory.genusCovolBound_trace_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:31:46.470589+00:00
-- url     : https://prove2.me/theorems/74456c9d-5787-4381-8c66-b8586f182a34
-- title:
--   Hermitian Lattices Theory: genus Covol Bound trace int
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol Bound trace int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovolBound.lean#L266-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovolBound.lean#L266-L271

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLatticesTheory.genusCovolBound_trace_int (r : 𝓞 K) :
    ∃ z : ℤ, Algebra.trace ℚ K (algebraMap (𝓞 K) K r) = z := by sorry
