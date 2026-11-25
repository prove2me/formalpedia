-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_jet_iterG
-- name    : Formalism.L2.FormalSeriesBounds.VP.jet_iterG
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:14.396387+00:00
-- url     : https://prove2.me/theorems/0c553bc0-bf0c-4148-8836-66e475e19d1d
-- title:
--   VP: jet iter G
-- statement:
--   The VP construction uses the jet iter G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L95-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L95-L108

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Var : Type} [Fintype Var] {n : ℕ}
variable (Y : FBChart C V O dd) (M : Var → Fin n × Fin dd → C)

theorem Formalism.L2.FormalSeriesBounds.VP.jet_iterG (b0 : Fin n) (u : Fin dd → C) (c : Var → C)
    (hc : ∀ b i, ∑ x, c x * M x (b, i) = if b = b0 then u i else 0) (k : ℕ) :
    ∀ (q : MvPolynomial Var C) (g : PS C n dd),
      jetAt0 q (linPull Y M ((DofN (Y.B.FK C) b0 u)^[k] g)) =
        jetAt0 (q * (∑ x, MvPolynomial.C (c x) * MvPolynomial.X x) ^ k) (linPull Y M g) := by sorry
