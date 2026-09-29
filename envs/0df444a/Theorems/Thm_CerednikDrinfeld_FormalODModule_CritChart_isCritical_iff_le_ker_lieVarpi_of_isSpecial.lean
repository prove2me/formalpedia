-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_iff_le_ker_lieVarpi_of_isSpecial
-- name    : CerednikDrinfeld.FormalODModule.CritChart.isCritical_iff_le_ker_lieVarpi_of_isSpecial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/9f1841f2-bd94-5a33-9973-6e9a11008ea7
-- title:
--   Critical index criterion on the Lie algebra for special formal mathcal O_D-modules
-- statement:
--   Let $p$ be a prime, $K$ a field of characteristic $p$, $j\colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to K$ a ring homomorphism, and $X$ a formal $\mathcal O_D$-module over $K$, that is: a two-dimensional commutative formal group law $X.F$ over $K$ together with an action of $\mathbb{Z}_{p^2}$ and an endomorphism $\varpi$ by law homomorphisms, satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$ for the Witt Frobenius $\sigma$. Write $\mathrm{Lie}\,X$ for the tangent module, $X.\mathrm{lieVarpi}$ for the endomorphism of $\mathrm{Lie}\,X$ given by the linear part of $\varpi$, and $X.\mathrm{lieZero}\,j$, $X.\mathrm{lieOne}\,j$ for the submodules on which every $a \in \mathbb{Z}_{p^2}$ acts through $j(a)$, respectively through $j(\sigma(a))$. Assume $X$ is special with respect to $j$: these two submodules are complementary in $\mathrm{Lie}\,X$ and each is an invertible $K$-module. The conclusion is a pair of equivalences, for $i=0$ and $i=1$: the index $i$ is critical — meaning that for every element $m$ of the $i$-th graded piece of the Cartier module of $X.F$ (those $m$ with $\mathrm{endAct}$ of the Teichmüller lift of each $c \in \mathbb{F}_{p^2}$ acting on $m$ as the homothety by $j(\tau(c))^{p^i}$) the element $\varpi\cdot m$ lies in the image of the Verschiebung — if and only if $X.\mathrm{lieVarpi}$ vanishes on $X.\mathrm{lieZero}\,j$, respectively on $X.\mathrm{lieOne}\,j$.
--
--   This is the dictionary between the Cartier-module and the Lie-algebra description of a critical index for a special formal $\mathcal O_D$-module over a field of characteristic $p$, as in Boutot–Carayol. It is used to transfer criticality statements formulated on Lie algebras (strata of Drinfeld's moduli problem, criticality of a base point) to the fibre computations with Cartier modules, and is cited in the analysis of the $\eta$-pieces over algebraically closed base fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_iff_le_ker_lieVarpi_of_isSpecial.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.FormalODModule.CritChart.isCritical_iff_le_ker_lieVarpi_of_isSpecial
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [CharP K p]
    (j : CerednikDrinfeld.Zp2 p →+* K) (X : CerednikDrinfeld.FormalODModule p K)
    (hX : X.IsSpecial j) :
    (CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j 0 ↔
        X.lieZero j ≤ LinearMap.ker X.lieVarpi) ∧
    (CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j 1 ↔
        X.lieOne j ≤ LinearMap.ker X.lieVarpi) := by sorry
