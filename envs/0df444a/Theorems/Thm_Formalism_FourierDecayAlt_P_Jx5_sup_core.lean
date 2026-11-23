-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_sup_core
-- name    : Formalism.FourierDecayAlt.P.Jx5.sup_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:39.994097+00:00
-- url     : https://prove2.me/theorems/3ebaebfd-70bd-4976-b499-0df767ef401e
-- title:
--   Jx5: sup core
-- statement:
--   The Jx5 construction uses the sup core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L8-L20

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx5

theorem Formalism.FourierDecayAlt.P.Jx5.sup_core {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (w : ι)
    (hg : 0 < G.g) (hk : 0 < G.ka) (S : Set ℝ) :
    sSup ((fun Y => G.g ^ G.m * (G.place w).be G.ka de de' T T' Y) '' S) /
        (G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹) =
      sSup ((fun Y => (G.place w).core de de' T T' Y) '' S) := by sorry
