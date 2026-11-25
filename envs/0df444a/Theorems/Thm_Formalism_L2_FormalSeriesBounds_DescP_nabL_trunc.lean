-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_nabL_trunc
-- name    : Formalism.L2.FormalSeriesBounds.DescP.nabL_trunc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:32:16.521121+00:00
-- url     : https://prove2.me/theorems/4229ab2a-3211-4537-b408-e1b556f08c1c
-- title:
--   Desc P: nab L trunc
-- statement:
--   The Desc P construction uses the nab L trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L166-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L166-L178

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

theorem Formalism.L2.FormalSeriesBounds.DescP.nabL_trunc (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (G : PS k n d) (f : PS k n d) :
    nabL F cp u P G f = ∑ μ ∈ (trunc' k (cst P.totalDegree) f).support,
      MvPolynomial.coeff μ (trunc' k (cst P.totalDegree) f) * nabL F cp u P G (monomial μ (1 : k)) := by sorry
