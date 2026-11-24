-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_Sym_const_ev
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:44.694835+00:00
-- url     : https://prove2.me/theorems/0332a0d8-7057-4ba5-9847-db039dcb6457
-- title:
--   Sym: const ev
-- statement:
--   The Sym construction uses the const ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CPfSym.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CPfSym.lean#L88-L91

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
variable {k : Type} [CommRing k]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev {m n d : ℕ} (a : Fin m → Pt k n d) (ha : ∀ p q, constantCoeff (a p q) = 0) (g : PS k m d) :
    constantCoeff (ev a g) = constantCoeff g := by sorry
