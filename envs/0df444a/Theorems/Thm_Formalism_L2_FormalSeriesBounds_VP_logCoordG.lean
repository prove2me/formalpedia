-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_logCoordG
-- name    : Formalism.L2.FormalSeriesBounds.VP.logCoordG
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:22:29.860133+00:00
-- url     : https://prove2.me/theorems/37854ebc-4500-488a-b5ce-a738408c68b2
-- title:
--   VP: log Coord G
-- statement:
--   The VP construction uses the log Coord G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L132-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L132-L152

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

theorem Formalism.L2.FormalSeriesBounds.VP.logCoordG {ι : Type} [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (P : MvPolynomial ι C)
    (co : ι → Var → C)
    (hco : ∀ ℓ ∈ P.vars, ∀ b i, ∑ x, co ℓ x * M x (b, i) = if b = cp ℓ then uv ℓ i else 0) (F : PS C n dd) :
    MvPowerSeries.constantCoeff (DpolyN (Y.B.FK C) cp uv P F) =
      jetAt0 (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (co ℓ x) * MvPolynomial.X x) P) (linPull Y M F) := by sorry
