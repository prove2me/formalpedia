-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_cgen
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.val_cgen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:18.41281+00:00
-- url     : https://prove2.me/theorems/85367c6e-c79d-4b29-b896-f18918421af9
-- title:
--   Germ B: val cgen
-- statement:
--   The Germ B construction uses the val cgen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBGen.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBGen.lean#L63-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.val_cgen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i0 : L.ι) (h0 : LB.wchart L φ (fun _ => i0) = ⊤) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    val (cgen L φ ε (fun _ => i0) h0) r z J = ∏ k, cv L i0 z J (r ≫ φ k) ^ ε k := by sorry
