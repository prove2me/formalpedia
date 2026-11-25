-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_coe_eq_sum
-- name    : Formalism.L2.FormalSeriesBounds.DescP.coe_eq_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:12.753424+00:00
-- url     : https://prove2.me/theorems/c6fe755f-1136-4c89-9460-3280dcd7e8a7
-- title:
--   Desc P: coe eq sum
-- statement:
--   The Desc P construction uses the coe eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L156-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L156-L164

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.DescP
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {n d : ℕ}

theorem Formalism.L2.FormalSeriesBounds.DescP.coe_eq_sum (p : MvPolynomial (Fin n × Fin d) k) :
    (p : PS k n d) = ∑ μ ∈ p.support, MvPolynomial.coeff μ p • monomial μ (1 : k) := by sorry
