-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_Nst_eq
-- name    : Formalism.FourierDecayAlt.P.PBA.Nst_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:53:37.479002+00:00
-- url     : https://prove2.me/theorems/34cb38bd-c5ab-4a3d-bbce-1cc1a6cc0a76
-- title:
--   PBA: Nst eq
-- statement:
--   The PBA construction uses the Nst eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L87-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L87-L97

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)

theorem Formalism.FourierDecayAlt.P.PBA.Nst_eq {ε : ℝ} {i : ℕ} (hi : i ≤ S.G.r + 1) (s : ℕ) (w : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : E) :
    S.base.Nst ε i s w Y κ t t' = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, KB.gN S v ε i (w.1 v)
      (C.loc (S.σ v) h ++ [(s, S.σ v t)]) (C.loc (S.σ v) h' ++ [(s, S.σ v t')]) := by sorry
