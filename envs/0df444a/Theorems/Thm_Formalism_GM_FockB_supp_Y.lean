-- Prove2me | Theorems.Thm_Formalism_GM_FockB_supp_Y
-- name    : Formalism.GM.FockB.supp_Y
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:58.258996+00:00
-- url     : https://prove2.me/theorems/b89a7396-f66a-4c8a-8c5b-7060810dd224
-- title:
--   Fock B: supp Y
-- statement:
--   The Fock B construction uses the supp Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L583-L591
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L583-L591

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.FockB.supp_Y {t : ℕ} (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (g : MvPolynomial (BVar N r t) ℚ_[p])
    (m : BVar N r t →₀ ℕ) (hm : m ∈ (rename (chainEmb N r t) y * g).support) :
    ∃ m1 ∈ y.support, ∃ m2 ∈ g.support, m = Finsupp.mapDomain (chainEmb N r t) m1 + m2 := by sorry
