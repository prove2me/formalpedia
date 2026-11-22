-- Prove2me | Theorems.Thm_Formalism_IndefR_Rat_coord_rat
-- name    : Formalism.IndefR.Rat.coord_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:33:19.444812+00:00
-- url     : https://prove2.me/theorems/48e0e2f4-31f9-4dce-a445-c3645b47fd6d
-- title:
--   Rat: coord rat
-- statement:
--   The Rat construction uses the coord rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/RationalAdjoints/CoordRat.lean#L9-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/RationalAdjoints/CoordRat.lean#L9-L62

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_RationalAdjoints_CoordRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Rat
open Matrix

theorem Formalism.IndefR.Rat.coord_rat {K : Type} [Field K] (σ : K →+* ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] {κ : Type} [Fintype κ]
    [DecidableEq κ] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : κ → Module.Dual ℂ E) (hψ : ∀ e, (∀ i, ψ i e = 0) → e = 0)
    (f : (ι → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f)
    (hfr : ∀ i l, ψ i (f (Pi.single l 1)) ∈ Set.range σ)
    (c : ι → ℂ) (hc : ∀ i, ψ i (f c) ∈ Set.range σ) : ∀ l, c l ∈ Set.range σ := by sorry
