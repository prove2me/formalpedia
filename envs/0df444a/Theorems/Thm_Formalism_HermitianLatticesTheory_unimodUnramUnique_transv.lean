-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_transv
-- name    : Formalism.HermitianLatticesTheory.unimodUnramUnique_transv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:39.71878+00:00
-- url     : https://prove2.me/theorems/837e07ab-ae08-4551-af85-24b06264b12e
-- title:
--   Hermitian Lattices Theory: unimod Unram Unique transv
-- statement:
--   The Hermitian Lattices Theory construction uses the unimod Unram Unique transv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L290-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L290-L296

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
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
open Polynomial IsLocalRing Matrix
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}

theorem Formalism.HermitianLatticesTheory.unimodUnramUnique_transv {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R)
    (i j : ι) (c : R) :
    ((transvection j i c)ᴴ * A * transvection j i c) i i
      = A i i + (c * A i j + star c * A j i) + star c * c * A j j := by sorry
