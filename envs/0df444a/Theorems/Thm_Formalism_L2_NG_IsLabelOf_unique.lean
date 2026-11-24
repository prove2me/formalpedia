-- Prove2me | Theorems.Thm_Formalism_L2_NG_IsLabelOf_unique
-- name    : Formalism.L2.NG.IsLabelOf.unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:10:27.61968+00:00
-- url     : https://prove2.me/theorems/d48ca9c8-618b-47e4-b91a-5c2c71029911
-- title:
--   Is Label Of: unique
-- statement:
--   The Is Label Of construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsLab.lean#L85-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsLab.lean#L85-L94

import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.L2 Formalism.L2.NG
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {p : ℕ} [Fact p.Prime]
variable {A : ValuationSubring Ω} {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {ζ : ℕ → Formalism.CyclotomicNorms.Fbar p}
  {teich : Formalism.CyclotomicNorms.Fbar p →* ℂ} {I : Set (Ω ≃ₐ[E] Ω)} {n : ℕ} {P : (Ω ≃ₐ[E] Ω) → ℂ[X]} {f f' : (ZMod p)[X]}

theorem Formalism.L2.NG.IsLabelOf.unique (h : IsLabelOf A κ ζ teich I n P f) (h' : IsLabelOf A κ ζ teich I n P f')
    (ht : Function.Injective teich) {σ : Ω ≃ₐ[E] Ω} (hσ : σ ∈ I) (hc : NT.TameCoupled A κ σ ζ) : f = f' := by sorry
