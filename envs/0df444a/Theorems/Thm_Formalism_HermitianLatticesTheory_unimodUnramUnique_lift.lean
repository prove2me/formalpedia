-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_lift
-- name    : Formalism.HermitianLatticesTheory.unimodUnramUnique_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:33.72382+00:00
-- url     : https://prove2.me/theorems/0ef0e310-1fd8-4f69-9c6f-9385a2e6da5e
-- title:
--   Hermitian Lattices Theory: unimod Unram Unique lift
-- statement:
--   The Hermitian Lattices Theory construction uses the unimod Unram Unique lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L14-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L14-L30

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

theorem Formalism.HermitianLatticesTheory.unimodUnramUnique_lift (T N d s₀ t₀ : S)
    (h0 : s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d ∈ maximalIdeal S)
    (h1 : IsUnit (2 * s₀ + T * t₀)) :
    ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by sorry
