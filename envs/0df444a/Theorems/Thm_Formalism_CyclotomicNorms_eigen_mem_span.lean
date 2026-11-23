-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_eigen_mem_span
-- name    : Formalism.CyclotomicNorms.eigen_mem_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:25.098803+00:00
-- url     : https://prove2.me/theorems/3ff16571-d6ce-44bc-9275-ee8e077c6b3b
-- title:
--   Cyclotomic Norms: eigen mem span
-- statement:
--   The Cyclotomic Norms construction uses the eigen mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/RestrictionOfBlocksAndJordan.lean#L25-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/RestrictionOfBlocksAndJordan.lean#L25-L43

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

theorem Formalism.CyclotomicNorms.eigen_mem_span (ρ : Representation k G V) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → G → k) (I : Subgroup G) (he : ∀ i, ∀ y ∈ I, ρ y (e i) = χ i y • e i)
    (hsep : ∀ i j, i ≠ j → ∃ y ∈ I, χ i y ≠ χ j y)
    (j : Fin N) (v : V) (hv : ∀ y ∈ I, ρ y v = χ j y • v) : v ∈ k ∙ e j := by sorry
