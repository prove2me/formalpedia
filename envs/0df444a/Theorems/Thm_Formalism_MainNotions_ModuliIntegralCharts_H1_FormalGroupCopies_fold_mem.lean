-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_fold_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.fold_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:02.341654+00:00
-- url     : https://prove2.me/theorems/ccc542d5-6080-4470-aa47-0aabd2d1d12f
-- title:
--   Formal Group Copies: fold mem
-- statement:
--   The Formal Group Copies construction uses the fold mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupCopies.lean#L127-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupCopies.lean#L127-L138

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.fold_mem (T : Finset (Fin n)) (mm : ι →₀ ℕ) (hm : ∀ l, mm l ≠ 0 → cp l ∈ T) (L : List ι)
    (A : PS R n d) (hA : A ∈ subV R (Vc d T)) :
    L.foldr (fun l g => (DofN F (cp l) (u l))^[mm l] g) A ∈ subV R (Vc d T) := by sorry
