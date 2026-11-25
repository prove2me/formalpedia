-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_CapelliExpansionLemmas_quantum_minor_border_expansion_first
-- name    : Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas.quantum_minor_border_expansion_first
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:09:52.448059+00:00
-- url     : https://prove2.me/theorems/2982a57d-ba19-5ae5-95b8-c8ecc6513007
-- title:
--   Capelli Expansion Lemmas: quantum minor border expansion first
-- statement:
--   The Capelli Expansion Lemmas construction uses the quantum minor border expansion first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHatJDRStepABorder.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHatJDRStepABorder.lean#L13-L28

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BorderedDeterminants
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatJDRStepABorder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas.quantum_minor_border_expansion_first {n m : ℕ} (E : Fin n → Fin n → A) (e : Fin n) (f b : Fin m → Fin n) (hE : GlRel E)
    (hf : ∀ j, f j ≠ e) (hb : ∀ j, b j ≠ e) (u : ℂ) :
    qminor E (bE e f) (bE e b) u = Tm E u e e * qminor E f b (u - 1) -
      ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E (f w) e * qminor E (f ∘ skip1 w) (b ∘ skip1 x) (u - 2) * E e (b x)) := by sorry
