-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_one_of_lieOne_le_ker_lieVarpi
-- name    : CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_one_of_lieOne_le_ker_lieVarpi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/d6b54358-997b-568b-8cf1-ded8a846ed05
-- title:
--   Lie-level vanishing gives index-1 criticality after base change
-- statement:
--   Fix a prime $p$ and a commutative ring $B$, a ring homomorphism $j \colon \mathrm{Zp2}\,p \to B$ from the Witt vectors of the field with $p^2$ elements, and a formal $\mathcal{O}_D$-module $X$ over $B$, i.e. a commutative two-dimensional formal group law $X.F$ over $B$ together with an action `act` of $\mathrm{Zp2}\,p$ by endomorphism series and a series `varpi` satisfying $\varpi\circ\varpi = \mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a) = \mathrm{act}(\sigma a)\circ\varpi$ for the Witt-vector Frobenius $\sigma$. Assume that the two submodules of the Lie module $X.\mathrm{Lie}$ cut out by the eigenvalue conditions are complementary, namely $\mathrm{lieZero}\ j\ X = \bigcap_a \ker(\mathrm{lieAct}\,a - j(a))$ and $\mathrm{lieOne}\ j\ X = \bigcap_a \ker(\mathrm{lieAct}\,a - j(\sigma a))$ satisfy `IsCompl`, and assume $\mathrm{lieOne}\ j\ X \subseteq \ker(\mathrm{lieVarpi})$, where $\mathrm{lieVarpi}$ is multiplication by the linear part of the matrix of $\varpi$. Let $B'$ be a commutative ring of characteristic $p$ and $f \colon B \to B'$ a ring homomorphism. The conclusion is that the base-changed module $X.\mathrm{map}\ f$ over $B'$, with structure map $f \circ j$, satisfies `CritChart.IsCritical` in degree $1$: for every $m$ in the degree-$1$ graded piece `gradedPiece` of the Cartier module of $(X.\mathrm{map}\ f).F$ there exists $g$ in that Cartier module with $V g = \varpi \cdot m$, the action of the endomorphism `varpiEnd`.
--
--   This is the index-$1$ half of the criticality criterion used in the Čerednik–Drinfeld uniformisation package: a tangent-level condition on the $\sigma$-eigenspace of the Lie module of a formal $\mathcal{O}_D$-module guarantees, after any base change to characteristic $p$, that $\varpi$ carries the degree-$1$ part of the Cartier module into the image of the Verschiebung. It feeds the construction of $\eta$-sections and of the edge isogenies attached to the Bruhat–Tits tree, where `IsCritical` is an input hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_one_of_lieOne_le_ker_lieVarpi.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_one_of_lieOne_le_ker_lieVarpi
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (j : Zp2 p →+* B) (X : FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j))
    (h : X.lieOne j ≤ LinearMap.ker X.lieVarpi)
    {B' : Type} [CommRing B'] [CharP B' p] (f : B →+* B') :
    FormalODModule.CritChart.IsCritical (X.map f) (f.comp j) 1 := by sorry
