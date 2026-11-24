-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_split
-- name    : Formalism.HermitianLatticesTheory.unimodUnramUnique_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:26.223885+00:00
-- url     : https://prove2.me/theorems/4b335977-b6a6-45a4-a7f9-c189d3069dec
-- title:
--   Hermitian Lattices Theory: unimod Unram Unique split
-- statement:
--   The Hermitian Lattices Theory construction uses the unimod Unram Unique split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L32-L36

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
variable {S : Type*} [CommRing S] [HenselianLocalRing S]

theorem Formalism.HermitianLatticesTheory.unimodUnramUnique_split (T N d r : S) (hr : r ^ 2 + T * r + N = 0)
    (hu : IsUnit (T + 2 * r)) : ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by sorry
