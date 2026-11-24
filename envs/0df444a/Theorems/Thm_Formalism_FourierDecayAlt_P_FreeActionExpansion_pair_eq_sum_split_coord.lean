-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FreeActionExpansion_pair_eq_sum_split_coord
-- name    : Formalism.FourierDecayAlt.P.FreeActionExpansion.pair_eq_sum_split_coord
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:57.008185+00:00
-- url     : https://prove2.me/theorems/6e21b81f-c465-497f-af83-4dec84c14ff4
-- title:
--   Free Action Expansion: pair eq sum split coord
-- statement:
--   The Free Action Expansion construction uses the pair eq sum split coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeActionExpansion.lean#L116-L119

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

theorem Formalism.FourierDecayAlt.P.FreeActionExpansion.pair_eq_sum_split_coord (a : S) (ρ : Rep A V) (Ψ Ψ' : Ix S → V) :
    pair ρ Ψ Ψ' = ∑ u, if u a = 0 then ρ.β (Ψ u) (Ψ' u) +
      ρ.β (Ψ (Function.update u a 1)) (Ψ' (Function.update u a 1)) else 0 := by sorry
