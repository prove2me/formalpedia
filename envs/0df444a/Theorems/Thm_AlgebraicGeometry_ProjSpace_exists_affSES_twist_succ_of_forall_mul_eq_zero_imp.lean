-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp
-- name    : AlgebraicGeometry.ProjSpace.exists_affSES_twist_succ_of_forall_mul_eq_zero_imp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/371eb792-05f9-58c5-91a5-6225c2e9359a
-- title:
--   Hyperplane short exact sequence of twists, with Čech comparison
-- statement:
--   Fix $n \in \mathbb{N}$ and a commutative ring $k$, and write $\mathbb{P}^n_k = \operatorname{Proj}$ of the graded ring of homogeneous submodules of $k[X_0,\dots,X_n]$. Let $\iota_k : Z_k \to \mathbb{P}^n_k$ be a closed immersion, and let $\ell$ be homogeneous of degree $1$ such that for every $i$ the section $\iota_k^{\sharp}(\ell/X_i)$ of $\mathcal{O}_{Z_k}$ over $\iota_k^{-1}D_+(X_i)$ is a non-zero-divisor. Let $\mathcal{I}_\ell$ be ideal sheaf data on $\mathbb{P}^n_k$ whose ideal on each affine chart $D_+(X_i)$ is spanned by the sections $G/X_i^{d}$ with $G$ homogeneous of degree $d$ lying in the ideal $(\ell)$, and let $\iota' : Z' \to \mathbb{P}^n_k$ be a closed immersion with $\ker \iota' = \ker \iota_k \sqcup \mathcal{I}_\ell$. Then for every $d \in \mathbb{N}$ there exist a presheaf of modules $\mathcal{F}_3$ over the structure morphism $\iota_k$ followed by $\pi$, and maps $\mathrm{inc} : \mathcal{O}_{Z_k}(d) \to \mathcal{O}_{Z_k}(d+1)$, $\mathrm{proj} : \mathcal{O}_{Z_k}(d+1) \to \mathcal{F}_3$ of such presheaves (in the sense of the twist presheaves `ProjSpace.twist`) which on every affine open are respectively injective and surjective with range of $\mathrm{inc}$ equal to the kernel of $\mathrm{proj}$; together with $k$-linear isomorphisms $e_0$ between the Čech $0$-cocycles of $\mathcal{F}_3$ on the pullback of the standard cover to $Z_k$ and those of $\mathcal{O}_{Z'}(d+1)$ on its pullback to $Z'$, and $k$-linear isomorphisms in each degree $i$ between the corresponding quotients $\ker d^{i+1}/\operatorname{im} d^{i}$ for $\mathcal{F}_3$ on $Z_k$ and for $\mathcal{O}_{Z'}(d+1)$ on $Z'$; and these may be chosen so that, for every Čech $0$-cocycle $c$ of $\mathcal{O}_{Z_k}(d+1)$ and every homogeneous $G$ of degree $d+1$ whose frames $G/X_i^{d+1}$ pulled back along $\iota_k$ give all components of $c$, the image of $c$ under $\mathrm{proj}$ and then $e_0$ has all components given by the frames $G/X_i^{d+1}$ pulled back along $\iota'$.
--
--   This is the hyperplane section sequence $0 \to \mathcal{O}_Z(d) \to \mathcal{O}_Z(d+1) \to \mathcal{O}_{Z \cap V(\ell)}(d+1) \to 0$ for a linear form $\ell$ that is a non-zero-divisor on $Z$, in the form of an affine-wise exact sequence of twist presheaves together with an identification of the Čech cohomology of the third term with that of the twist on $Z' = Z \cap V(\ell)$, compatible with the classes of homogeneous forms of degree $d+1$. It feeds the inductive bound on higher Čech cohomology and on degree-$(d+1)$ sections used in the analysis of maximal Hilbert-function growth.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_affSES_twist_succ_of_forall_mul_eq_zero_imp
    (n : ℕ) (k : Type) [CommRing k]
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk]
    (ℓ : MvPolynomial (Fin (n + 1)) k) (hℓ : ℓ.IsHomogeneous 1)
    (hnzd : ∀ (i : Fin (n + 1)) (t : Γ(Zk, ιk ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))),
      (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
          (HomogeneousLocalization.mk
            { deg := 1
              num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
              den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow i 1)⟩
              den_mem := ⟨1, rfl⟩ }))) * t = 0 → t = 0)
    (𝓘ℓ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).IdealSheafData)
    (h𝓘ℓ : (∀ i : Fin (n + 1),
        𝓘ℓ.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i) (ProjSpace.X_mem_one k n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (G : MvPolynomial (Fin (n + 1)) k) (hG : G.IsHomogeneous d),
          G ∈ Ideal.span {ℓ} ∧
          s = Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG⟩
                  den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }))
    (Z' : Scheme.{0}) (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι']
    (hker : ι'.ker = ιk.ker ⊔ 𝓘ℓ) (d : ℕ) :
    ∃ (F₃ : OModulePresheaf (ιk ≫ ProjSpace.π k n))
      (S : OModulePresheaf.AffSES (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d)
        (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)) F₃)
      (e₀ : F₃.H0 (ProjSpace.stdCoverPullback ιk) ≃ₗ[k]
        (ProjSpace.twist (ι' ≫ ProjSpace.π k n) ι' (d + 1)).H0 (ProjSpace.stdCoverPullback ι'))
      (_e : ∀ i : ℕ, F₃.HSucc (ProjSpace.stdCoverPullback ιk) i ≃ₗ[k]
        (ProjSpace.twist (ι' ≫ ProjSpace.π k n) ι' (d + 1)).HSucc (ProjSpace.stdCoverPullback ι') i),

      ∀ (c : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).cochain (ProjSpace.stdCoverPullback ιk) 0)
        (hc : c ∈ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).H0 (ProjSpace.stdCoverPullback ιk))
        (G : MvPolynomial (Fin (n + 1)) k) (hG : G.IsHomogeneous (d + 1)),
          (∀ (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
            (c s).val i =
              ProjSpace.restrictFun
                (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i ≤
                  ProjSpace.pullbackChart ιk i)
                (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d + 1
                    num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule (d + 1) G).mpr hG⟩
                    den := ⟨MvPolynomial.X i ^ (d + 1), (MvPolynomial.mem_homogeneousSubmodule (d + 1) _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i (d + 1))⟩
                    den_mem := ⟨d + 1, rfl⟩ })))) →
          ∀ (s : (ProjSpace.stdCoverPullback ι').Idx 0) (i : Fin (n + 1)),
            ((e₀ (S.proj.H0Map (ProjSpace.stdCoverPullback ιk) ⟨c, hc⟩)).1 s).val i =
              ProjSpace.restrictFun
                (inf_le_right : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' i ≤
                  ProjSpace.pullbackChart ι' i)
                (ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d + 1
                    num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule (d + 1) G).mpr hG⟩
                    den := ⟨MvPolynomial.X i ^ (d + 1), (MvPolynomial.mem_homogeneousSubmodule (d + 1) _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i (d + 1))⟩
                    den_mem := ⟨d + 1, rfl⟩ }))) := by sorry
