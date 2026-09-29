-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_colH_biCech_equiv_pi_cech_restrict
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_colH_biCech_equiv_pi_cech_restrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/d14e0dde-b632-5698-89db-7e6925ef2da3
-- title:
--   Bi-Čech columns as products of Čech cohomologies
-- statement:
--   Let $R$ be a commutative ring, $Z$ a scheme, $\pi : Z \to \operatorname{Spec} R$ a morphism, and $N$ a sheaf of $\mathcal{O}_Z$-modules. Let $\mathfrak{A}$ and $\mathfrak{B}$ be ordered open families on $Z$, each consisting of a finite linearly ordered index type together with a family of opens of $Z$, and fix $p \in \mathbb{N}$. Write $\mathfrak{A}.\mathrm{Idx}\,p$ for the strictly monotone maps $\mathrm{Fin}(p+1) \to \mathfrak{A}.\iota$ and, for such a chain $s$, let $\mathfrak{A}.\mathrm{inter}\,s = \bigsqcap_j \mathfrak{A}.U(s_j)$, regarded as an open subscheme of $Z$ via its inclusion $\iota_s$. Assume given, for each $s$, an ordered affine cover $\mathfrak{W}_s$ of that open subscheme (a finite linearly ordered family of affine opens with supremum $\top$), an order isomorphism $e_s : \mathfrak{B}.\iota \simeq (\mathfrak{W}_s).\iota$, and the compatibility that $\iota_s$ carries the chart $(\mathfrak{W}_s).U(e_s j)$ onto the open $\mathfrak{A}.\mathrm{inter}\,s \sqcap \mathfrak{B}.U(j)$ of $Z$ for every $j$. The conclusion is twofold. First, the vertical cohomology at $(p,0)$ of the bi-Čech double complex of the presheaf of modules `ofModules π N` with respect to $\mathfrak{A}, \mathfrak{B}$ — that is, $\ker(\mathrm{dV}\,p\,0)$, the subquotient by $\bot$ — admits an $R$-linear isomorphism onto the product over all chains $s$ of the zeroth Čech module $\mathrm{H}^0$ of `ofModules (ι_s ≫ π) (N.restrict ι_s)` on $\mathfrak{W}_s$, i.e. the kernel of the degree-$0$ Čech differential. Second, for every $q$, the vertical cohomology at $(p, q+1)$ admits an $R$-linear isomorphism onto the product over $s$ of the corresponding alternating Čech cohomology $\mathrm{HSucc}\ q$ of the restricted data on $\mathfrak{W}_s$. Both assertions are stated as nonemptiness of the relevant types of linear equivalences, so no particular isomorphism is singled out.
--
--   This is the standard identification of the columns of a bi-Čech double complex: the $p$-th column, with differential in the $\mathfrak{B}$-direction, splits as a product over the $\mathfrak{A}$-chains $s$ of the alternating Čech complex of $N|_{\mathfrak{A}_s}$ for the affine cover of $\mathfrak{A}_s$ cut out by $\mathfrak{B}$, so its vertical cohomology is the product of the Čech cohomologies of the restrictions. It feeds the computation of the Euler characteristic of a Mumford bundle twisted by a pullback as an alternating sum of lengths.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_colH_biCech_equiv_pi_cech_restrict.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_colH_biCech_equiv_pi_cech_restrict
    {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of R)) (N : Z.Modules)
    (𝔄 𝔅 : Z.OrderedOpenFamily) (p : ℕ)
    (𝔚 : ∀ s : 𝔄.Idx p, ((𝔄.inter s : Z.Opens) : Scheme.{u}).OrderedAffineCover)
    (e : ∀ s : 𝔄.Idx p, 𝔅.ι ≃o (𝔚 s).ι)
    (h𝔚 : ∀ (s : 𝔄.Idx p) (j : 𝔅.ι), (𝔄.inter s).ι ''ᵁ (𝔚 s).U (e s j) = 𝔄.inter s ⊓ 𝔅.U j) :
    Nonempty (DoubleComplex.colH ((OModulePresheaf.ofModules π N).biCech 𝔄 𝔅) p 0 ≃ₗ[R]
        (∀ s : 𝔄.Idx p, ↥((OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).H0 (𝔚 s)))) ∧
      ∀ q : ℕ, Nonempty (DoubleComplex.colH ((OModulePresheaf.ofModules π N).biCech 𝔄 𝔅) p (q + 1) ≃ₗ[R]
        (∀ s : 𝔄.Idx p, (OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).HSucc (𝔚 s) q)) := by sorry
