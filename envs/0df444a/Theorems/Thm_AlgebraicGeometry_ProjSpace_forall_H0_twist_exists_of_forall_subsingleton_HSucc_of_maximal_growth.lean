-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth
-- name    : AlgebraicGeometry.ProjSpace.forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/4a6b44a8-de3c-55cc-9cbc-5a939bf955c6
-- title:
--   Degree-d forms surject onto Čech H⁰ under maximal growth
-- statement:
--   Fix $n,m\in\mathbb N$ with $1\le m$, a field $k$ (in the base universe), and an ideal $J\subseteq k[X_0,\dots,X_n]$ that admits a generating set consisting of forms of degree $m$ (hypothesis `hJ`). Write `piece J d` for the quotient of the space of forms of degree $d$ by those lying in $J$, i.e. the degree-$d$ piece of $k[X_0,\dots,X_n]/J$; assume maximal growth at $m$, namely $\dim_k$ `piece J (m+1)` $=$ [`Nat.macaulayPow m`](def/Nat_MacaulayPow.html#L7) applied to $\dim_k$ `piece J m`, where [`Nat.macaulayPow`](def/Nat_MacaulayPow.html#L7) is Macaulay's maximal-growth operator defined by the recursion on binomial expansions. Let $\iota_k : Z_k \to \operatorname{Proj} k[X_0,\dots,X_n]$ be a closed immersion of schemes, and assume: (`hZ`) for every $d\ge m$ and every form $F$ of degree $d$, one has $F\in J$ if and only if for each $i$ the pullback along $\iota_k$ of the section $F/X_i^{\,d}$ of $\mathcal O(d)$ over the basic open $D(X_i)$ vanishes; and (`hvan`) for every $d\ge m$ and every $i$, the module `HSucc` of the twisted presheaf `ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d` relative to the ordered affine cover `ProjSpace.stdCoverPullback ιk` (the preimages under $\iota_k$ of the standard charts $D(X_j)$) at level $i$ is a subsingleton — that is, all Čech cohomology of $\mathcal O_{Z}(d)$ for this cover in positive degrees vanishes, $\ker d_{i+1}$ being contained in the image of $d_i$. The conclusion: for every $d\ge m$ and every element $c$ of the degree-zero Čech cohomology `H0` of that twisted presheaf for that cover (a $0$-cochain annihilated by the first Čech differential), there is a form $F$ of degree $d$ with, for every $0$-simplex $s$ of the cover and every $i\in\mathrm{Fin}(n+1)$, the $i$-th chartwise component $(c\,s).\mathrm{val}\,i$ equal to the restriction to `inter s ⊓ pullbackChart ιk i` of the pullback along $\iota_k$ of $F/X_i^{\,d}$. In other words, the map from degree-$d$ forms to Čech global sections of $\mathcal O_{Z_k}(d)$ is surjective for all $d\ge m$.
--
--   This is the cohomological half of Gotzmann-type regularity: under Čech-acyclicity of the twists and maximal growth of the Hilbert function of $k[X]/J$ in degree $m$, every global section of $\mathcal O_{Z}(d)$ in degrees $d\ge m$ comes from a form of degree $d$, the argument comparing the Hilbert polynomial of $k[X]/J$ with the Euler characteristic of $\mathcal O_Z(d)$. It feeds the combined statement [`AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth`](thm.html#AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth), used in the regularity bounds for the Hilbert-functor construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth
    (n m : ℕ) (hm : 1 ≤ m) (k : Type) [Field k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) k), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank k (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank k (piece J m)))
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk]
    (hZ : (∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ J ↔ ∀ i : Fin (n + 1), (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0)))
    (hvan : ∀ d : ℕ, m ≤ d → (∀ i : ℕ, Subsingleton
          ((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).HSucc (ProjSpace.stdCoverPullback ιk) i))) :
    ∀ d : ℕ, m ≤ d →
      (∀ c ∈ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk),
          ∃ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
            ∀ (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
              (c s).val i =
                ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i ≤
                    ProjSpace.pullbackChart ιk i)
                  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) := by sorry
