-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_semi
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.semi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:59:08.20312+00:00
-- url     : https://prove2.me/theorems/2c181d67-f777-49b2-9cef-1871d7c2c646
-- title:
--   SC: semi
-- statement:
--   The SC construction uses the semi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PStdChar.lean#L228-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PStdChar.lean#L228-L248

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
variable (L : PeriodPair) (d : ℕ)
local notation "EE" => Formalism.L2.Th1.F.altE L
variable {L d}
variable (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.semi :
    (∀ x ∈ L.lattice, ∃ m : ℤ, q1 L d x = (m : ℝ)) ∧ (∀ x ∈ L.lattice, aa L d x = 1 ∨ aa L d x = -1) ∧
    ∀ x ∈ L.lattice, ∀ y ∈ L.lattice, aa L d (x + y) = aa L d x * aa L d y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (EE x y : ℂ)) := by sorry
