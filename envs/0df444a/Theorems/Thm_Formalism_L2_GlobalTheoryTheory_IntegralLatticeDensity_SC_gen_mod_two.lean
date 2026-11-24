-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_gen_mod_two
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.gen_mod_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:59:13.075464+00:00
-- url     : https://prove2.me/theorems/8b288d40-7eec-4c44-96d9-89de58849923
-- title:
--   SC: gen mod two
-- statement:
--   The SC construction uses the gen mod two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PStdChar.lean#L32-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PStdChar.lean#L32-L67

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.gen_mod_two (L : PeriodPair) (x y w : ℂ) (hx : x ∈ L.lattice) (hy : y ∈ L.lattice) (hw : w ∈ L.lattice)
    (h1 : x / 2 ∉ L.lattice) (h2 : y / 2 ∉ L.lattice) (h3 : (x + y) / 2 ∉ L.lattice) :
    ∃ v ∈ L.lattice, w = 2 * v ∨ w = x + 2 * v ∨ w = y + 2 * v ∨ w = x + y + 2 * v := by sorry
