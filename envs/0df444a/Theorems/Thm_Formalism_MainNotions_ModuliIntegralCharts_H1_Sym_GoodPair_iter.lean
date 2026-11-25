-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_Sym_GoodPair_iter
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.GoodPair.iter
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:39.516879+00:00
-- url     : https://prove2.me/theorems/93e7679e-c4b6-4a4d-aed8-c17304dcc163
-- title:
--   Good Pair: iter
-- statement:
--   The Good Pair construction uses the iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CPfSym.lean#L40-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CPfSym.lean#L40-L60

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LegendreSumSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CPfSym
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.Sym
variable {k : Type} [CommRing k] {σ : Type}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.GoodPair.iter {D D₀ : MvPowerSeries σ k → MvPowerSeries σ k} (hP : GoodPair D D₀) (c : ℕ) :
    ∀ r g, OrdGE (c + r) g →
      OrdGE (r + 1) (D^[c] g - D₀^[c] g) ∧ OrdGE r (D^[c] g) ∧ OrdGE r (D₀^[c] g) := by sorry
