-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_HTot_biCech_equiv_prodCover_of_isQuasicoherent
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_HTot_biCech_equiv_prodCover_of_isQuasicoherent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/e17acf9a-995b-5963-9e55-082fd5e9a4c8
-- title:
--   Bi-Čech total cohomology computes Čech cohomology of the product cover
-- statement:
--   Let $R$ be a commutative ring, $Z$ a scheme and $\pi\colon Z\to\operatorname{Spec}R$ a separated morphism, and let $N$ be an $\mathcal O_Z$-module. Write $F$ for the associated presheaf of $R$-modules $U\mapsto\Gamma(N,U)$ with the restriction maps, and assume $F$ satisfies `IsQuasicoherent`: for every affine open $U\subseteq Z$ and every $f\in\Gamma(Z,U)$, each section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$. Let $\mathfrak A$ and $\mathfrak B$ be two `OrderedOpenFamily`s, i.e. finite linearly ordered index sets together with families of opens $\mathfrak A.U_i$, $\mathfrak B.U_j$ of $Z$, such that every $\mathfrak A.U_i\sqcap\mathfrak B.U_j$ is affine open (`haff`) and $\bigsqcup_{i,j}\mathfrak A.U_i\sqcap\mathfrak B.U_j=\top$ (`hcov`). Let $D=F.\mathrm{biCech}\,\mathfrak A\,\mathfrak B$ be the bounded bi-Čech double complex attached to the two families, with horizontal and vertical differentials `BiCech.dH`, `BiCech.dV` and vanishing bound $\max(|\mathfrak A.\iota|,|\mathfrak B.\iota|)$, and let $\mathfrak A\boxtimes\mathfrak B=\mathfrak A.\mathrm{prodCover}\,\mathfrak B$ be the ordered affine cover with index $\mathfrak A.\iota\times_{\mathrm{lex}}\mathfrak B.\iota$ and opens $\mathfrak A.U_i\sqcap\mathfrak B.U_j$. The conclusion asserts the existence (as nonemptiness of the corresponding types) of $R$-linear isomorphisms $\mathrm{HTot}(D,0)\cong F.H0(\mathfrak A\boxtimes\mathfrak B)=\ker(F.d\,0)$, and, for every $n$, $\mathrm{HTot}(D,n+1)\cong F.\mathrm{HSucc}(\mathfrak A\boxtimes\mathfrak B)\,n=\ker(F.d\,(n+1))/\operatorname{im}(F.d\,n)$; here $\mathrm{HTot}(D,n)$ is $\ker(\mathrm{dTot}\,n)$ modulo the image of $\mathrm{dTot}\,(n-1)$ (by convention $\bot$ for $n=0$).
--
--   This is the comparison, for a quasi-coherent module on a separated scheme, between the cohomology of the total complex of the double Čech complex of two open families and the ordered Čech cohomology of their common refinement $(\mathfrak A.U_i\cap\mathfrak B.U_j)_{i,j}$ — the Eilenberg–Zilber type statement that the total complex of a bi-Čech complex computes the Čech cohomology of the product cover. It is the bridge that lets later results about Čech cohomology of affine covers (vanishing, finiteness of ranks, base change) be transported to the bi-Čech double complex.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_HTot_biCech_equiv_prodCover_of_isQuasicoherent.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_HTot_biCech_equiv_prodCover_of_isQuasicoherent
    {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (N : Z.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)
    (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (hcov : ⨆ ij : 𝔄.ι × 𝔅.ι, 𝔄.U ij.1 ⊓ 𝔅.U ij.2 = ⊤) :
    Nonempty (DoubleComplex.HTot ((OModulePresheaf.ofModules π N).biCech 𝔄 𝔅) 0 ≃ₗ[R]
        (OModulePresheaf.ofModules π N).H0 (𝔄.prodCover 𝔅 haff hcov)) ∧
      ∀ n : ℕ, Nonempty (DoubleComplex.HTot ((OModulePresheaf.ofModules π N).biCech 𝔄 𝔅) (n + 1) ≃ₗ[R]
        (OModulePresheaf.ofModules π N).HSucc (𝔄.prodCover 𝔅 haff hcov) n) := by sorry
