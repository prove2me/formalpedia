-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_stdChar_eq
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.stdChar_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:52.187065+00:00
-- url     : https://prove2.me/theorems/d76c718b-5175-4dac-a272-913f68f6f8b7
-- title:
--   SC: std Char eq
-- statement:
--   The SC construction uses the std Char eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PStdChar.lean#L354-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PStdChar.lean#L354-L359

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
variable {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) (hθ : cmTheta 1 d * (ω₀ / 2) ∉ L.lattice)
  (hθ' : (1 - cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice)
include h0 hθ hθ'

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.stdChar_eq (hd : d % 8 = 7) (n : Type) [Fintype n] [DecidableEq n] (x : n → ℂ) (hx : x ∈ stdLat L n) :
    alphaQ (Real.sqrt d / 2) (stdH L n) x = stdChar L ω₀ x := by sorry
