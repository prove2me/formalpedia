-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_zero_of_lieZero_le_ker_lieVarpi
-- name    : CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_zero_of_lieZero_le_ker_lieVarpi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/67d0e888-b0d4-5214-9ff7-4e29a3c00ffe
-- title:
--   Lie-level vanishing yields index-0 criticality after base change
-- statement:
--   Fix a prime $p$, a commutative ring $B$, a ring homomorphism $j$ from $\mathbb{Z}_{p^2} =$ `Zp2 p` (the Witt vectors of $\mathbb{F}_{p^2}$) to $B$, and a formal $\mathcal{O}_D$-module $X$ over $B$ in the sense of the structure `FormalODModule`: a $2$-variable formal group law $X.F$ over $B$, together with a commutativity witness, an action $a \mapsto X.\mathrm{act}\,a$ of $\mathbb{Z}_{p^2}$ by endomorphisms of $X.F$ and a further endomorphism $X.\varpi$, subject to $\mathrm{act}\,1 = \mathrm{id}$, multiplicativity and additivity of $\mathrm{act}$, $\varpi \circ \varpi = \mathrm{act}\,p$ and $\varpi \circ \mathrm{act}\,a = \mathrm{act}(\sigma a) \circ \varpi$ for the Witt-vector Frobenius $\sigma$. Two hypotheses are imposed on $X$: first, that the submodules $X.\mathrm{lieZero}\,j = \bigcap_{a} \ker(\mathrm{lieAct}\,a - j(a)\cdot\mathrm{id})$ and $X.\mathrm{lieOne}\,j = \bigcap_{a} \ker(\mathrm{lieAct}\,a - j(\sigma a)\cdot\mathrm{id})$ of the tangent module $X.\mathrm{Lie}$ are complementary; second, that $X.\mathrm{lieZero}\,j$ is annihilated by $X.\mathrm{lieVarpi}$, the endomorphism of $X.\mathrm{Lie}$ given by multiplication with the linear-part matrix of $X.\varpi$. Let further $B'$ be a commutative ring of characteristic $p$ and $f : B \to B'$ a ring homomorphism. The conclusion is that the base-changed module $X.\mathrm{map}\,f$ over $B'$, with structure map $f \circ j$, is critical in index $0$: for every $m$ in the graded piece $\mathrm{gradedPiece}\,(f\circ j)\,0$ of the Cartier module of $(X.\mathrm{map}\,f).F$ there is a $g$ in that Cartier module with $V g = \varpi\cdot m$, where $V$ is the Verschiebung and $\varpi\cdot m$ denotes the action of the endomorphism $(X.\mathrm{map}\,f).\mathrm{varpiEnd}$ on $m$.
--
--   This is the passage from a tangent-space (Lie-algebra) condition on a formal $\mathcal{O}_D$-module to the Cartier-module criticality condition used in the chart-by-chart analysis of the Čerednik–Drinfeld uniformisation, in the index-$0$ component of the $\mathbb{Z}/2$-grading. It is the input for the constructions of $\eta$-sections and of the critical-index charts attached to edges and nodes of the Mumford model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_zero_of_lieZero_le_ker_lieVarpi.lean

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

theorem CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_zero_of_lieZero_le_ker_lieVarpi
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (j : Zp2 p →+* B) (X : FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j))
    (h : X.lieZero j ≤ LinearMap.ker X.lieVarpi)
    {B' : Type} [CommRing B'] [CharP B' p] (f : B →+* B') :
    FormalODModule.CritChart.IsCritical (X.map f) (f.comp j) 0 := by sorry
