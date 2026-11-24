-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_exists_max_above
-- name    : Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.exists_max_above
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:12.362794+00:00
-- url     : https://prove2.me/theorems/adb34702-5cf8-4f06-9882-45d6e26fb81b
-- title:
--   Dual Lattice Index Bis: exists max above
-- statement:
--   The Dual Lattice Index Bis construction uses the exists max above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L235-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L235-L260

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis

theorem Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.exists_max_above (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)) (p : ℕ) (hp : p.Prime)
    (hI : p ∣ Ideal.absNorm I) (h0 : Ideal.absNorm I ≠ 0) :
    ∃ P : Ideal (𝓞 E), P.IsMaximal ∧ I ≤ P ∧ ((p : ℕ) : 𝓞 E) ∈ P := by sorry
