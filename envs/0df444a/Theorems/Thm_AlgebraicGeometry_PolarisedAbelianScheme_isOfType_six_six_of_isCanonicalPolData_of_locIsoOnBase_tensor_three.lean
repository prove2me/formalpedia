-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_isOfType_six_six_of_isCanonicalPolData_of_locIsoOnBase_tensor_three
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.isOfType_six_six_of_isCanonicalPolData_of_locIsoOnBase_tensor_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/80fe8596-d6cc-5e0a-89b6-5b6c1ea668ec
-- title:
--   Polarisation of type (6,6) from a cube of canonical polarisation data
-- statement:
--   Let $S$ be a commutative ring in which $6$ is a unit, let $d,n$ be natural numbers and let $u$ be a polarised abelian scheme of relative dimension $2$ over $S$: a scheme $A$ with a morphism $f \colon A \to \operatorname{Spec} S$, a commutative relative group law $L$, the abelian-scheme property bundle for $f$, all fibres of topological Krull dimension $2$, four $n$-torsion sections that are independent and span the $n$-torsion on every algebraically closed geometric fibre, together with an invertible module $u.\mathrm{pol}$ on $A$ which is a closed immersion by its sections over $S$ and whose geometric fibrewise $H^0$ has rank $d$. Let $I$ be a type, $act \colon I \to (A \to A)$ a family of endomorphisms over $\operatorname{Spec} S$ ($act\,x$ followed by $f$ equals $f$), $star \colon I \to I$, and let $polE$ be a module on $A$ satisfying [`CerednikDrinfeld.QM.IsCanonicalPolData`](def/CerednikDrinfeld_QMCanonicalPol.html#L15) for $(f,L,act,star)$, i.e. $polE$ is invertible, symmetric (its pullback along the inversion morphism is locally on the base isomorphic to it), its kernel is exactly the $2$-torsion (the pullback of the Mumford bundle of $polE$ along the slice at a point $y$ of $A$ over any base change is locally on the base trivial if and only if $L$-doubling $y$ gives the unit section), it admits after a faithfully flat base change $S \to S'$ a decomposition $\mathcal L_0 \otimes (-1)^*\mathcal L_0$ with $\mathcal L_0$ invertible of trivial kernel (for every relative group law on the base change compatible with $L$ along the first projection), it has positive geometric fibrewise $H^0$ rank, and it is Rosati-compatible with $act$ and $star$. Assume finally that $u.\mathrm{pol}$ and $polE \otimes polE \otimes polE$ are locally isomorphic on the base: every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ over which the two modules become isomorphic after pullback to $f^{-1}U$. Then $u$ is of type $![6,6]$: there are a commutative ring $S'$, faithfully flat and étale as an $S$-algebra, and a map $x$ from $(\mathbb Z/6)^2 \times (\mathbb Z/6)^2$ to the $\operatorname{Spec} S'$-points of $f$ which is a homomorphism for $L$, is injective after composition with any map to an algebraically closed field, and whose image is exactly the kernel of $u.\mathrm{pol}$ in the following sense: for every $S'$-algebra $R$ and every $R$-point $y$ of $A$, the pullback of the Mumford bundle of $u.\mathrm{pol}$ along the slice at $y$ is locally on $\operatorname{Spec} R$ trivial if and only if there are finitely many elements of $R$ generating the unit ideal such that over each of the corresponding localisations $y$ agrees with $x\,h$ for some $h$. Of the clauses of `IsCanonicalPolData`, the proof uses only the invertibility of $polE$ and the description of its kernel as the $2$-torsion.
--
--   This is the step passing from a canonical (Čerednik–Drinfel'd quaternionic) polarisation datum $\mathcal L_E$ with $K(\mathcal L_E) = A[2]$ to the statement that a polarisation locally isomorphic to $\mathcal L_E^{\otimes 3}$ has kernel $A[6] \cong (\mathbb Z/6)^4$, i.e. is of type $(6,6)$ on an étale faithfully flat cover. It feeds the construction of rooted symmetric data of type $(6,6)$ for quaternionic multiplication structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_isOfType_six_six_of_isCanonicalPolData_of_locIsoOnBase_tensor_three.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.PolarisedAbelianScheme.isOfType_six_six_of_isCanonicalPolData_of_locIsoOnBase_tensor_three
    {d n : ℕ} {S : Type} [CommRing S] (h6 : IsUnit (6 : S)) (u : PolarisedAbelianScheme 2 d n S)
    {I : Type} (act : I → (u.A ⟶ u.A)) (act_over : ∀ x : I, act x ≫ u.f = u.f) (star : I → I)
    (polE : u.A.Modules) (hE : CerednikDrinfeld.QM.IsCanonicalPolData u.f u.L act act_over star polE)
    (hloc : LocIsoOnBase u.f u.pol (polE ⊗ polE ⊗ polE)) :
    PolarisedAbelianScheme.IsOfType ![6, 6] u := by sorry
