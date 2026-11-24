-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_ff
-- name    : Formalism.HermitianLatticesTheory.unimodUnramUnique_ff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:23.479155+00:00
-- url     : https://prove2.me/theorems/b7f0a2b6-9afd-4288-a08e-d1925572150e
-- title:
--   Hermitian Lattices Theory: unimod Unram Unique ff
-- statement:
--   The Hermitian Lattices Theory construction uses the unimod Unram Unique ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L38-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L38-L55

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

theorem Formalism.HermitianLatticesTheory.unimodUnramUnique_ff {k : Type*} [Field k] [Finite k] (T N d : k)
    (hD : T ^ 2 - 4 * N ≠ 0) : ∃ a b : k, a ^ 2 + T * a * b + N * b ^ 2 = d := by sorry
