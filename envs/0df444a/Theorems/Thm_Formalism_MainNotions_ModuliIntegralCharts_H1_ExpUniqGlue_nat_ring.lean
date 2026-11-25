-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_nat_ring
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.nat_ring
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:38:55.166586+00:00
-- url     : https://prove2.me/theorems/d1774a44-6b1a-4755-b39c-f5cfabb26cd2
-- title:
--   Exp Uniq Glue: nat ring
-- statement:
--   The Exp Uniq Glue construction uses the nat ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqGlue.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqGlue.lean#L44-L55

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
attribute [local instance] Over.cartesianMonoidalCategory
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.nat_ring {κ : Type} {m : ℕ} {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra T B']
    (ψ : Jet S κ m →ₐ[S] B) (ψ' : Jet T κ m →ₐ[T] B') (bB : B →+* B')
    (hB : ∀ s, bB (algebraMap S B s) = algebraMap T B' (f s)) (h : ∀ j, ψ' (zz m j) = bB (ψ (zz m j))) :
    (ψ' : Jet T κ m →+* B').comp (bcJ f κ m) = bB.comp (ψ : Jet S κ m →+* B) := by sorry
