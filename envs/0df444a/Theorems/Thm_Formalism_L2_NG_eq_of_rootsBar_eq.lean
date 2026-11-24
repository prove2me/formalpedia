-- Prove2me | Theorems.Thm_Formalism_L2_NG_eq_of_rootsBar_eq
-- name    : Formalism.L2.NG.eq_of_rootsBar_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:51.600808+00:00
-- url     : https://prove2.me/theorems/c57607f1-e704-4013-82c7-8c761a2df70b
-- title:
--   NG: eq of roots Bar eq
-- statement:
--   The NG construction uses the eq of roots Bar eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsLab.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsLab.lean#L78-L83

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

theorem Formalism.L2.NG.eq_of_rootsBar_eq (hf : f.Monic) (hf' : f'.Monic) (h : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar f') : f = f' := by sorry
