-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_pe_trunc
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.pe_trunc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:29.403523+00:00
-- url     : https://prove2.me/theorems/b3c20f12-d12e-462f-a35c-80edf3af5ebc
-- title:
--   Germ B: pe trunc
-- statement:
--   The Germ B construction uses the pe trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBSer.lean#L197-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBSer.lean#L197-L231

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.pe_trunc {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {e : ∀ m, FrTyG t x0 d x m} (htr : FrTrunc t x0 d x e) {n : ℕ}
    (φ : ℕ → Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (hφ : ∀ m i j, φ (m + 1) i j - φ m i j ∈ orig S (Fin n × Fin d) ^ (m + 1))
    (m : ℕ) (y : (jOG x0 d m n).left) (J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L y J) :
    val (peG t x0 d x e (m + 1) (φ (m + 1))) (ρn x0 d n m).left y J = val (peG t x0 d x e m (φ m)) (𝟙 _) y J := by sorry
