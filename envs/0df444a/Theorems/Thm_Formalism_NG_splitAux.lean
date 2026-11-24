-- Prove2me | Theorems.Thm_Formalism_NG_splitAux
-- name    : Formalism.NG.splitAux
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:15.286648+00:00
-- url     : https://prove2.me/theorems/fd4b4cfe-22dc-41e7-b390-e926d801eb5e
-- title:
--   NG: split Aux
-- statement:
--   The NG construction uses the split Aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SplitFibre.lean#L127-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SplitFibre.lean#L127-L137

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SplitFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
universe u

theorem Formalism.NG.splitAux (n : ℕ) : ∀ (T : Type u) [CommRing T] (P : T[X]), P.Monic → P.natDegree = n →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (rr : Fin n → T'),
      Module.Free T T' ∧ Module.Finite T T' ∧ Module.finrank T T' = n.factorial ∧
      P.map (algebraMap T T') = ∏ i, (X - C (rr i)) ∧
      Algebra.adjoin T (Set.range rr) = ⊤ ∧
      ∀ (B : Type u) [CommRing B] [Algebra T B] (a : Fin n → B),
        P.map (algebraMap T B) = ∏ i, (X - C (a i)) →
        ∃ φ : T' →ₐ[T] B, ∀ i, φ (rr i) = a i := by sorry
