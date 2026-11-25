-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_zetaMul_eq_sum
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_zetaMul_eq_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:27:16.315634+00:00
-- url     : https://prove2.me/theorems/77d86b90-c9bd-5bd1-9338-627c5cd72f4a
-- title:
--   Primes In Progressions: dhpr zeta Mul eq sum
-- statement:
--   The Primes In Progressions construction uses the dhpr zeta Mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeA.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeA.lean#L71-L79

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation ComplexOrder
set_option backward.isDefEq.respectTransparency.types false

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_zetaMul_eq_sum {M : ℕ} (χ : DirichletCharacter ℂ M) (n : ℕ) :
    zetaMul χ n = ∑ d ∈ n.divisors, χ (d : ZMod M) := by sorry
