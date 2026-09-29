-- Prove2me | Theorems.Thm_AlgebraicCurve_cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections
-- name    : AlgebraicCurve.cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/1cb514f8-fb7b-5b6c-93e3-e250fc7995a6
-- title:
--   Cover independence of the Čech-to-répartition map in H¹(0)
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra, and let $\mathrm{Place}\ K\ F$ denote the places of $F/K$, i.e. the valuation subrings of $F$ that contain the image of $K$, are not all of $F$, and are principal ideal rings; for a set $S$ of such places and the zero divisor, $\mathtt{lSpaceOn}\ S\ 0$ is the $K$-submodule $\{h \in F : v(h) \le 1 \text{ for all } v \in S\}$ of functions with no pole on $S$, where $v$ is the adic valuation attached to the place. Suppose given two pairs of place-sets $(S_0,S_1)$ and $(T_0,T_1)$, each covering all places, i.e. $S_0 \cup S_1 = T_0 \cup T_1 = \mathrm{univ}$; an element $f$ of $\mathtt{lSpaceOn}(S_0 \cap S_1)\,0$ and an element $f'$ of $\mathtt{lSpaceOn}(T_0 \cap T_1)\,0$; and four elements $g_{00}, g_{01}, g_{10}, g_{11}$ of $F$ with $g_{ij} \in \mathtt{lSpaceOn}(S_i \cap T_j)\,0$, satisfying $g_{00} = g_{10} + f$, $g_{01} = g_{11} + f$ and $g_{01} = g_{00} + f'$. Then the classes of $f$ and of $f'$ in the respective Čech quotients $\mathtt{lSpaceOn}(S_0 \cap S_1)\,0 / \mathrm{range}(\mathtt{cechDiff}\ S_0\ S_1\ 0)$ and $\mathtt{lSpaceOn}(T_0 \cap T_1)\,0 / \mathrm{range}(\mathtt{cechDiff}\ T_0\ T_1\ 0)$ have the same image under the comparison maps $\mathtt{cechH1ToH1}$, namely in $H^1(0)$, the répartitions modulo the sum of the everywhere-integral répartitions and the principal ones; here $\mathtt{cechH1ToH1}\ hS\ 0$ is induced by sending $f$ to the class of the répartition that is $0$ at the places of $S_0$ and $f$ elsewhere.
--
--   This is the function-field, répartition-theoretic form of the independence of a Čech $H^1(X,\mathcal O_X)$ class from the two-chart cover used to compute it: the $g_{ij}$ are the cross sections on the four sets $S_i \cap T_j$ of the common refinement witnessing that $f$ and $f'$ become cohomologous there. It is used in the relative Picard machinery, in [`AlgebraicGeometry.RelPicard.IsDeformationClassMap.cechH1ToH1_germ_eq_of_two_covers`](thm.html#AlgebraicGeometry.RelPicard.IsDeformationClassMap.cechH1ToH1_germ_eq_of_two_covers) and in the comparison of germs with traces along a cover for fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {S₀ S₁ T₀ T₁ : Set (Place K F)} (hS : S₀ ∪ S₁ = Set.univ) (hT : T₀ ∪ T₁ = Set.univ)
    (f : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F))) (f' : ↥(lSpaceOn (T₀ ∩ T₁) (0 : Divisor K F)))
    (g₀₀ g₀₁ g₁₀ g₁₁ : F)
    (h₀₀ : g₀₀ ∈ lSpaceOn (S₀ ∩ T₀) (0 : Divisor K F)) (h₀₁ : g₀₁ ∈ lSpaceOn (S₀ ∩ T₁) (0 : Divisor K F))
    (h₁₀ : g₁₀ ∈ lSpaceOn (S₁ ∩ T₀) (0 : Divisor K F)) (h₁₁ : g₁₁ ∈ lSpaceOn (S₁ ∩ T₁) (0 : Divisor K F))
    (e₀ : g₀₀ = g₁₀ + (f : F)) (e₁ : g₀₁ = g₁₁ + (f : F)) (e₀' : g₀₁ = g₀₀ + (f' : F)) :
    cechH1ToH1 hS 0 (Submodule.Quotient.mk f) = cechH1ToH1 hT 0 (Submodule.Quotient.mk f') := by sorry
