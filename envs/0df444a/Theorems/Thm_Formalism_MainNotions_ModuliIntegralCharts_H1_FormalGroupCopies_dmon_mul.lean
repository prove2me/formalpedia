-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_dmon_mul
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.dmon_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:11:09.236076+00:00
-- url     : https://prove2.me/theorems/2cd47e13-079f-441d-b050-cfa21ba4f80a
-- title:
--   Formal Group Copies: dmon mul
-- statement:
--   The Formal Group Copies construction uses the dmon mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupCopies.lean#L168-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupCopies.lean#L168-L173

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
variable {R : Type} [CommRing R] {d n : ℕ}
variable {ι : Type} [Fintype ι] (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.dmon_mul (S : Finset (Fin n)) (m₁ m₂ : ι →₀ ℕ) (hm1 : ∀ l, m₁ l ≠ 0 → cp l ∈ S)
    (hm2 : ∀ l, m₂ l ≠ 0 → cp l ∈ Sᶜ) (A B : PS R n d)
    (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DmonN F cp u (m₁ + m₂) (A * B) = DmonN F cp u m₁ A * DmonN F cp u m₂ B := by sorry
