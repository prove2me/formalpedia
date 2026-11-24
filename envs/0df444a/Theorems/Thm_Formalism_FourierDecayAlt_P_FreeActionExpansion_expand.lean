-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FreeActionExpansion_expand
-- name    : Formalism.FourierDecayAlt.P.FreeActionExpansion.expand
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:29.820246+00:00
-- url     : https://prove2.me/theorems/165ae229-7934-474f-97d6-9d3a6931d652
-- title:
--   Free Action Expansion: expand
-- statement:
--   The Free Action Expansion construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L128-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L128-L229

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FreeActionExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S]
  [DecidableEq S] [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem Formalism.FourierDecayAlt.P.FreeActionExpansion.expand (ρ : Rep A V) (QQ : ℂ → M2 A) (f : A) (s : ℂ) (w : List (Letter ℂ S))
    (vA vB vAv vBv : A[X]) (x : Ix S → V) (Ξ : F7.Sesq (Ix S → V))
    (hΞ : ∀ X X', Ξ X X' = frm ρ (RRw QQ w * Vw f s w) X X') (hx : SupportedOnUsedSlots w x) :
    ∀ L : List (Letter ℂ S), (∀ l ∈ L, l.plus = true ∧ l.pt.im = 0) → (L.map Letter.intersection_update_fsHerm_neg_one).Nodup →
      (∀ l ∈ L, l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one) → ∀ P P' : A,
      pair ρ (act (JL L * RRw QQ w * Vw f s (L ++ w)) (P • letters vA vB L x))
          (P' • letters vAv vBv (L.map dl) x) =
        F7.Fw Ξ x x (L.map fun l => ((⟨vA, vB, vAv, vBv, s⟩ : F7.Dat A), l.pt.re)) P P' := by sorry
