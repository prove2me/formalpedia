-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_span
-- name    : Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_span
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:12:30.796071+00:00
-- url     : https://prove2.me/theorems/2a6a1920-7b90-45f6-8dd4-acdc4b9c64a4
-- title:
--   Quadratic Basis: qb span
-- statement:
--   The Quadratic Basis construction uses the qb span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/QuadBasis.lean#L124-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/QuadBasis.lean#L124-L153

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
variable {W O : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]

theorem Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_span {p n' : ℕ} (hp : p.Prime) (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W))
    (cW : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hfin : j.Finite) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (cO : Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n'))
    (hθ : ∀ a : W, ¬ w ∣ θ - j a) (x : O) :
    ∃ a b c d : W, x = j a + j b * θ + j c * w + j d * θ * w := by sorry
