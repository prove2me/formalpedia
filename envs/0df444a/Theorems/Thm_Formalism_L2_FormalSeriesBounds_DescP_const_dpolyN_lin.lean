-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_const_dpolyN_lin
-- name    : Formalism.L2.FormalSeriesBounds.DescP.const_dpolyN_lin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:05.359184+00:00
-- url     : https://prove2.me/theorems/0f2580f3-3a1f-4d5f-ba70-720d9c6caffd
-- title:
--   Desc P: const dpoly N lin
-- statement:
--   The Desc P construction uses the const dpoly N lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L187-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L187-L203

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

theorem Formalism.L2.FormalSeriesBounds.DescP.const_dpolyN_lin (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    {α : Type} (s : Finset α) (c : α → k) (Q : α → MvPolynomial ι k) (g : PS k n d) :
    constantCoeff (DpolyN F cp u (∑ i ∈ s, c i • Q i) g) =
      ∑ i ∈ s, c i * constantCoeff (DpolyN F cp u (Q i) g) := by sorry
