-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_repr_diag_apply
-- name    : Formalism.CyclotomicNorms.repr_diag_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:48.446207+00:00
-- url     : https://prove2.me/theorems/9d1dd6d5-31e2-4544-ad18-4e220bdeef97
-- title:
--   Cyclotomic Norms: repr diag apply
-- statement:
--   The Cyclotomic Norms construction uses the repr diag apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/RestrictionOfBlocksAndJordan.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/RestrictionOfBlocksAndJordan.lean#L14-L23

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open Formalism Formalism.CyclotomicNorms
variable {G k V : Type} [Group G] [Field k] [AddCommGroup V] [Module k V] {N : ℕ}

theorem Formalism.CyclotomicNorms.repr_diag_apply (ρ : Representation k G V) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → G → k) (y : G) (hy : ∀ i, ρ y (e i) = χ i y • e i) (v : V) (m : Fin N) :
    e.repr (ρ y v) m = χ m y * e.repr v m := by sorry
