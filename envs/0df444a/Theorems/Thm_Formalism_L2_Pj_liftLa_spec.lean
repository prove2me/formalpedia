-- Prove2me | Theorems.Thm_Formalism_L2_Pj_liftLa_spec
-- name    : Formalism.L2.Pj.liftLa_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:38.648843+00:00
-- url     : https://prove2.me/theorems/1c1f0fa7-e873-48a0-abe1-cefc697e6f44
-- title:
--   Pj: lift La spec
-- statement:
--   The Pj construction uses the lift La spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LiftLaSpec.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LiftLaSpec.lean#L38-L42

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem Formalism.L2.Pj.liftLa_spec (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (a : Dw.La) :
    (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ (liftLa γ a) = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a) := by sorry
