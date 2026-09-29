-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf
-- name    : AlgebraicGeometry.Scheme.Modules.exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/840bc2ec-b7b2-5ceb-99d0-f2f38713ab6c
-- title:
--   Proj presentation of a cocycle-glued module with prescribed charts
-- statement:
--   Let $B$ be a commutative ring, $Y$ a scheme with a morphism $\pi_Y : Y \to \operatorname{Spec} B$, and let $V_0,\dots,V_{r-1}$ be affine opens of $Y$ with $\bigsqcup_i V_i = \top$ (supremum $\top$). Let $w_{ij} \in \Gamma(Y, V_i)$ satisfy $w_{ii} = 1$ and $Y_{w_{ij}} = V_i \cap V_j$ (basic open equal to the intersection), let $k > 0$, and let $c$ be a unit cocycle on $(V_i)$, i.e. sections $u_{ij} \in \Gamma(Y, V_i \cap V_j)$ with $u_{ii} = 1$ and $u_{ij}u_{jk} = u_{ik}$ on $V_i \cap V_j \cap V_k$, such that $u_{ij} = (w_{ij}|_{V_i \cap V_j})^k$. Let $N \in \mathbb{N}$ and let $a_{\alpha j} \in \Gamma(Y, V_j)$ ($\alpha \in \mathrm{Fin}(N+1)$, $j$ an index) satisfy $a_{\alpha j} = (w_{jm})^k\, a_{\alpha m}$ on $V_j \cap V_m$, and let $e$ be an injective map from the index set of the cover into $\mathrm{Fin}(N+1)$ with $a_{e(i)\,j} = w_{ji}^{\,k}$ in $\Gamma(Y, V_j)$ for all $i,j$. Then the module $\mathcal{N} = \mathtt{glueOfCocycle}\,c$ obtained by gluing the structure sheaf along $c$ (its sections over $T$ being the families $(x_i \in \Gamma(Y, T \cap V_i))$ with $x_i = u_{ij}x_j$ on $T \cap V_i \cap V_j$) admits a `ProjPresentation` $\mathfrak{P}$ relative to $\pi_Y$ of size $N$: global sections $\sigma_\alpha \in \Gamma(\mathcal{N}, \top)$, a morphism $\mathfrak{P}.\mathrm{toProj} : Y \to \operatorname{Proj}$ of the homogeneous coordinate algebra $B[x_0,\dots,x_N]$ with $\mathfrak{P}.\mathrm{toProj}$ followed by the projection to $\operatorname{Spec} B$ equal to $\pi_Y$, such that on every open $V$ contained in $\mathfrak{P}.\mathrm{toProj}^{-1}D_+(x_\alpha)$ multiplication by $\sigma_\alpha|_V$ is a bijection $\Gamma(Y,V) \to \Gamma(\mathcal{N},V)$, and the pullback of $x_\beta/x_\alpha$ times $\sigma_\alpha$ equals $\sigma_\beta$ over $\mathfrak{P}.\mathrm{toProj}^{-1}D_+(x_\alpha)$; and moreover the $j$-th component of $\sigma_\alpha$ is $a_{\alpha j}$ (restricted to $\top \cap V_j$), one has $V_i \le \mathfrak{P}.\mathrm{toProj}^{-1}D_+(x_{e(i)})$ with in fact $\mathfrak{P}.\mathrm{toProj}^{-1}D_+(x_{e(i)}) = V_i$, and the pullback along $\mathfrak{P}.\mathrm{toProj}$ of the section $x_\alpha/x_{e(i)}$ of $D_+(x_{e(i)})$ equals $a_{\alpha i}$ in $\Gamma(Y, V_i)$.
--
--   This is the construction, in the style of the classical criterion for a family of sections of an invertible sheaf to define a morphism to projective space, applied to the invertible module glued from a unit cocycle $u_{ij} = w_{ij}^k$ on a given affine cover: the resulting morphism to $\mathbb{P}^N_B$ has the given charts $V_i$ as the preimages of the standard basic opens $D_+(x_{e(i)})$, with prescribed coordinate ratios. It feeds [`AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`](thm.html#AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType), and rests on the general statement that frames on a cover yield a `ProjPresentation`, [`AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.Modules.exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf
    (B : Type) [CommRing B] (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of B))
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j)
    (k : ℕ) (hk : 0 < k) (c : Scheme.Modules.UnitCocycle V)
    (hc : ∀ i j : Fin r, c.u i j = Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) ^ k)
    (N : ℕ) (a : Fin (N + 1) → ∀ j : Fin r, Γ(Y, V j))
    (ha : ∀ (α : Fin (N + 1)) (j m : Fin r),
      Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (a α j) =
        Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
          Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (a α m))
    (e : Fin r → Fin (N + 1)) (he : Function.Injective e) (hae : ∀ i j : Fin r, a (e i) j = w j i ^ k) :
    ∃ 𝔓 : (Scheme.Modules.glueOfCocycle c).ProjPresentation πY N,
      (∀ (α : Fin (N + 1)) (j : Fin r), Scheme.Modules.glueComponent c ⊤ j (𝔓.σ α) =
        Y.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V j ≤ V j)).op (a α j)) ∧
      ∃ hV : ∀ i : Fin r, V i ≤ 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)),
        (∀ i : Fin r, 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)) = V i) ∧
        (∀ (i : Fin r) (α : Fin (N + 1)),
          𝔓.toProj.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)))
              (V i) (hV i)
            (Proj.awayToSection _ (MvPolynomial.X (e i)) (ProjSpace.ratio B N (e i) α)) = a α i) := by sorry
