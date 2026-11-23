-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_tvprod_map
-- name    : Formalism.FourierDecayAlt.P.RuleGD.tvprod_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:59.338633+00:00
-- url     : https://prove2.me/theorems/cb54d20c-43d9-4f8d-b13e-69bea5e677fb
-- title:
--   Rule GD: tvprod map
-- statement:
--   The Rule GD construction uses the tvprod map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L97-L101

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

theorem Formalism.FourierDecayAlt.P.RuleGD.tvprod_map (L : LevelData A r) (φ : A →+* A) (Y Y' : ℂ)
    (h : ∀ l, (L.Tvl Y l).map φ = L.Tvl Y' l) : (L.Tvprod Y).map φ = L.Tvprod Y' := by sorry
