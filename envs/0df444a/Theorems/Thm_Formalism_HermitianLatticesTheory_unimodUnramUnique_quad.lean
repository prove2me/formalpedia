-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_quad
-- name    : Formalism.HermitianLatticesTheory.unimodUnramUnique_quad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:04.797229+00:00
-- url     : https://prove2.me/theorems/a6a2565b-8512-413f-bf27-a273d309b8c6
-- title:
--   Hermitian Lattices Theory: unimod Unram Unique quad
-- statement:
--   The Hermitian Lattices Theory construction uses the unimod Unram Unique quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L57-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L57-L138

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

theorem Formalism.HermitianLatticesTheory.unimodUnramUnique_quad [Finite (ResidueField S)] (T N d : S)
    (hD : IsUnit (T ^ 2 - 4 * N)) (hd : IsUnit d) :
    ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by sorry
