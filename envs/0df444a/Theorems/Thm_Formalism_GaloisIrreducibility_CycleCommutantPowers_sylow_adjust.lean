-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_sylow_adjust
-- name    : Formalism.GaloisIrreducibility.CycleCommutantPowers.sylow_adjust
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:34.716805+00:00
-- url     : https://prove2.me/theorems/05c4ada0-7fa1-449d-99ee-43c99b2266ff
-- title:
--   Cycle Commutant Powers: sylow adjust
-- statement:
--   The Cycle Commutant Powers construction uses the sylow adjust property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L110-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/JordanPrime.lean#L110-L184

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Equiv Equiv.Perm MulAction
open Formalism.GaloisIrreducibility.CycleCommutantPowers
variable {α : Type} [Fintype α] [DecidableEq α]

theorem Formalism.GaloisIrreducibility.CycleCommutantPowers.sylow_adjust (G : Subgroup (Perm α)) (g : Perm α) (p : ℕ) (hp : p.Prime)
    (hgG : g ∈ G) (hgc : g.IsCycle) (hgp : g.support.card = p)
    (x : Perm α) (hxG : x ∈ G) (hxΓ : ∀ γ, g γ = γ → g (x⁻¹ γ) = x⁻¹ γ) :
    ∃ f ∈ G, (∀ γ, g γ = γ → f γ = γ) ∧ ∃ e : ℤ, (f * x) * g * (f * x)⁻¹ = g ^ e := by sorry
