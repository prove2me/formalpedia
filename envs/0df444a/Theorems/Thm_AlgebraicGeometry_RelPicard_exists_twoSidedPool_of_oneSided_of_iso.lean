-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoSidedPool_of_oneSided_of_iso
-- name    : AlgebraicGeometry.RelPicard.exists_twoSidedPool_of_oneSided_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/989706be-0f18-56d2-a384-42e2599240bf
-- title:
--   Two-sided pool from a one-sided pool and a swapping automorphism
-- statement:
--   Throughout, $R$ is a commutative ring, $c : C \to \operatorname{Spec} R$ is a morphism of schemes with $c$ separated, and $U$ is an open subscheme of $C$. The data $\varepsilon, \varepsilon'$ are elements of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, i.e. morphisms $\operatorname{Spec} R \to C$ composing with $c$ to the identity (sections of $c$), and $\sigma : C \cong C$ is an isomorphism with $\sigma$ followed by $c$ equal to $c$ (hypothesis `hσ`), so $\sigma$ is an automorphism over $\operatorname{Spec} R$. Three compatibility hypotheses are imposed: `hσε` says that $\varepsilon$ followed by $\sigma$ equals $\varepsilon'$; `hσU` says $\sigma^{-1}(U) = U$; and `hε'U` says the set-theoretic image of $\varepsilon'$ is contained in $U$. Finally $A_0, B_0, n_0$ are natural numbers and $f \in R$.
--
--   Notation for the base change along $f$: write $R_f :=$ `Localization.Away f`, let $C_f$ be the pullback of $c$ along $\operatorname{Spec} R_f \to \operatorname{Spec} R$, with first projection $\pi : C_f \to C$ and structure morphism $c_f : C_f \to \operatorname{Spec} R_f$ (the second projection, `baseChange R c (Localization.Away f)`), and let $\sigma_f : C_f \to C_f$ be the map `curveChange σ.hom hσ (specMap R (Localization.Away f))` induced by $\sigma$ and the identity of $\operatorname{Spec} R_f$. For a field $k$, assumed algebraically closed, and a morphism $s : \operatorname{Spec} k \to \operatorname{Spec} R_f$, write $C_s$ for the pullback of $c_f$ along $s$, with projections $p_s : C_s \to C_f$ and $q_s : C_s \to \operatorname{Spec} k$; put $U_s := (p_s \text{ followed by } \pi)^{-1}(U)$, an open subset of $C_s$; let $e_\varepsilon(s) \in C_s$ be the image of the closed point of $\operatorname{Spec} k$ under the $k$-point `sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s` of $C_s$ determined by $\varepsilon$, and similarly $e_{\varepsilon'}(s)$ for $\varepsilon'$; and let $\Gamma(s) :=$ `connectedComponentIn` $U_s\ e_\varepsilon(s)$, the connected component of $e_\varepsilon(s)$ inside $U_s$. Let $\sigma_s : C_s \to C_s$ be the map induced on the pullback by $\sigma_f$ together with the identities of $\operatorname{Spec} k$ and $\operatorname{Spec} R_f$.
--
--   The side-swapping hypothesis `hfar` requires, for every algebraically closed $k$ and every $s : \operatorname{Spec} k \to \operatorname{Spec} R_f$ such that $q_s$ is not smooth: first, that for every point $y$ of $C_s$ lying in $\Gamma(s)$ the image $\sigma_s(y)$ lies in $U_s \setminus \Gamma(s)$; and second, that $e_{\varepsilon'}(s) \in U_s \setminus \Gamma(s)$.
--
--   The one-sided pool data consist of: natural numbers $b, M$ with $A_0 b^{n_0} + B_0 < M$ (hypothesis `hM`); a commutative ring $R'$ which is an algebra over $R$ and over $R_f$ compatibly (scalar tower) and which is finite, étale and faithfully flat over $R_f$; a family $B : \mathrm{Fin}\,M \to \mathrm{Type}$ of commutative rings, each a finite étale $R_f$-algebra; degrees $\deg : \mathrm{Fin}\,M \to \mathbb{N}$ with $1 \le \deg i$ and $\deg i \le b$ for all $i$; $R'$-algebra isomorphisms $\varphi_i : R' \otimes_{R_f} B_i \cong R'^{\deg i}$; and closed immersions $z_i : \operatorname{Spec} B_i \to C_f$. These are subject to: `hz₁`, that $z_i$ followed by $c_f$ is the morphism $\operatorname{Spec} B_i \to \operatorname{Spec} R_f$ induced by the $R_f$-algebra structure of $B_i$; `hz₂`, that the image of $z_i$ lies in $\pi^{-1}(U)$; `hz₃`, that the images of $z_i$ and $z_j$ are disjoint for $i \ne j$; `hz₄`, that for every algebraically closed $k$, every $s$ and every $i$, the preimage $p_s^{-1}(\operatorname{im} z_i)$ is contained in $\Gamma(s)$ (no non-smoothness assumption on $q_s$ here); `hzinf` and `hzzero`, that the image of each $z_i$ is disjoint from the image of the base change of $\varepsilon$, respectively of $\varepsilon'$, to $C_f$; and `hzw`, that for all $i, j$ the image of $z_i$ is disjoint from the image of $z_j$ followed by $\sigma_f$.
--
--   The conclusion asserts the existence of natural numbers $b, M, M'$ (re-quantified, not necessarily the given ones) with $A_0 b^{n_0} + B_0 < M$ and $A_0 b^{n_0} + B_0 < M'$; of a ring $R'$ with commutative ring, $R$-algebra, $R_f$-algebra, scalar tower, finite, étale and faithfully flat structures over $R_f$; of a family $B : \mathrm{Fin}\,M \to \mathrm{Type}$ of commutative rings, each a finite étale $R_f$-algebra, degrees $\deg$ with $1 \le \deg i \le b$, $R'$-algebra isomorphisms $\varphi_i : R' \otimes_{R_f} B_i \cong R'^{\deg i}$ and closed immersions $z_i : \operatorname{Spec} B_i \to C_f$; and of a second family $B' : \mathrm{Fin}\,M' \to \mathrm{Type}$ of commutative rings, each a finite étale $R_f$-algebra, degrees $\deg'$ with $1 \le \deg' i \le b$, $R'$-algebra isomorphisms $\varphi'_i : R' \otimes_{R_f} B'_i \cong R'^{\deg' i}$ and closed immersions $z'_i : \operatorname{Spec} B'_i \to C_f$, such that the following nine conjuncts hold:
--
--   (1) each $z_i$ followed by $c_f$ is the morphism induced by the $R_f$-algebra structure of $B_i$; (2) the image of each $z_i$ lies in $\pi^{-1}(U)$; (3) the images of the $z_i$ are pairwise disjoint; (4) for every algebraically closed $k$, every $s : \operatorname{Spec} k \to \operatorname{Spec} R_f$ and every $i : \mathrm{Fin}\,M$, the preimage $p_s^{-1}(\operatorname{im} z_i)$ is contained in $\Gamma(s)$; (5) there is a $j$ with $\deg' j \le 1$; (6) each $z'_i$ followed by $c_f$ is the morphism induced by the $R_f$-algebra structure of $B'_i$; (7) the image of each $z'_i$ lies in $\pi^{-1}(U)$; (8) the images of the $z'_i$ are pairwise disjoint; (9) the image of $z_i$ is disjoint from the image of $z'_j$ for all $i$ and $j$; and finally, for every algebraically closed $k$, every $s : \operatorname{Spec} k \to \operatorname{Spec} R_f$ and every $i : \mathrm{Fin}\,M'$, if $q_s$ is not smooth then $p_s^{-1}(\operatorname{im} z'_i) \subseteq U_s \setminus \Gamma(s)$.
--
--   Thus the $z$-family in the conclusion satisfies the same conditions as the given one-sided pool except that disjointness from the two sections is not reasserted, while the new $z'$-family is a pool of the same degree bound $b$ containing a member of degree at most $1$ and concentrated, on non-smooth geometric fibres, in $U_s$ off the component of $\varepsilon$.
--
--   This is the passage from a one-sided étale pool of disjoint multisections lying on the $\varepsilon$-component of each geometric fibre to a two-sided pool, the second side being produced from the automorphism $\sigma$ (which carries the $\varepsilon$-component off itself on non-smooth fibres) together with the section $\varepsilon' = \sigma \circ \varepsilon$ as the member of degree at most one. It is used by the statements [`ModularCurve.XHDRModelAtP.exists_twoSidedPool_smoothLocus_closedPrime_two_of_atkinLehner_generic`](thm.html#ModularCurve.XHDRModelAtP.exists_twoSidedPool_smoothLocus_closedPrime_two_of_atkinLehner_generic), `…_three_of_atkinLehner_generic` and `…_of_five_le_of_atkinLehner_generic`, where $\sigma$ is an Atkin–Lehner involution of a model of a modular curve at $p$ and $U$ is its smooth locus, to supply the rigidifying data required by the relative Picard construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_twoSidedPool_of_oneSided_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve TensorProduct

theorem AlgebraicGeometry.RelPicard.exists_twoSidedPool_of_oneSided_of_iso
    (R : Type) [CommRing R] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    (ε ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (σ : C ≅ C) (hσ : σ.hom ≫ c = c)

    (hσε : ε.1 ≫ σ.hom = ε'.1) (hσU : σ.hom ⁻¹ᵁ U = U)
    [IsSeparated c] (hε'U : Set.range ε'.1.base ⊆ (U : Set C))
    (A₀ B₀ n₀ : ℕ) (f : R)
    (hfar : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))),
      ¬ Smooth (pullback.snd (baseChange R c (Localization.Away f)) s) →
      (∀ y : ↥(pullback (baseChange R c (Localization.Away f)) s),
        y ∈ connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k)) →
        (pullback.map (baseChange R c (Localization.Away f)) s (baseChange R c (Localization.Away f)) s
            (curveChange σ.hom hσ (specMap R (Localization.Away f))) (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (curveChange_snd _ _ _).symm)
            ((Category.comp_id _).trans (Category.id_comp _).symm)).base y ∈
          (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))) ∧
      ((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε') s).1).base (IsLocalRing.closedPoint k) ∈
          (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k)))
    (b M : ℕ) (hM : A₀ * b ^ n₀ + B₀ < M)
    (R' : Type) [CommRing R'] [Algebra R R'] [Algebra (Localization.Away f) R'] [IsScalarTower R (Localization.Away f) R']
    [Module.Finite (Localization.Away f) R'] [Algebra.Etale (Localization.Away f) R'] [Module.FaithfullyFlat (Localization.Away f) R']
    (B : Fin M → Type) [∀ i, CommRing (B i)] [∀ i, Algebra (Localization.Away f) (B i)]
    [∀ i, Module.Finite (Localization.Away f) (B i)] [∀ i, Algebra.Etale (Localization.Away f) (B i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (hdegb : ∀ i, deg i ≤ b)
    (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback c (specMap R (Localization.Away f)))
    [∀ i, IsClosedImmersion (z i)]
    (hz₁ : ∀ i, z i ≫ baseChange R c (Localization.Away f) = specMap (Localization.Away f) (B i))
    (hz₂ : ∀ i, Set.range (z i).base ⊆
      ((pullback.fst c (specMap R (Localization.Away f)) ⁻¹ᵁ U : (pullback c (specMap R (Localization.Away f))).Opens) :
        Set ↥(pullback c (specMap R (Localization.Away f)))))
    (hz₃ : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hz₄ : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange R c (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
              (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k)))
    (hzinf : ∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) ε).1.base))
    (hzzero : ∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) ε').1.base))
    (hzw : ∀ i j, Disjoint (Set.range (z i).base)
      (Set.range (z j ≫ curveChange σ.hom hσ (specMap R (Localization.Away f))).base)) :
    ∃ (b M M' : ℕ)
      (_ : A₀ * b ^ n₀ + B₀ < M) (_ : A₀ * b ^ n₀ + B₀ < M')
      (R' : Type) (_ : CommRing R') (_ : Algebra R R')
      (_ : Algebra (Localization.Away f) R') (_ : IsScalarTower R (Localization.Away f) R')
      (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
      (_ : Module.FaithfullyFlat (Localization.Away f) R')
      (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
      (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
      (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
      (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback c (specMap R (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z i))
      (B' : Fin M' → Type) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra (Localization.Away f) (B' i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B' i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B' i))
      (deg' : Fin M' → ℕ) (_ : ∀ i, 1 ≤ deg' i) (_ : ∀ i, deg' i ≤ b)
      (φ' : ∀ i, TensorProduct (Localization.Away f) R' (B' i) ≃ₐ[R'] (Fin (deg' i) → R'))
      (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ pullback c (specMap R (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z' i)),

      (∀ i, z i ≫ baseChange R c (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
      (∀ i, Set.range (z i).base ⊆
        ((pullback.fst c (specMap R (Localization.Away f)) ⁻¹ᵁ U : (pullback c (specMap R (Localization.Away f))).Opens) :
          Set ↥(pullback c (specMap R (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M),
        (pullback.fst (baseChange R c (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
          connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))) ∧

      (∃ j, deg' j ≤ 1) ∧
      (∀ i, z' i ≫ baseChange R c (Localization.Away f) = specMap (Localization.Away f) (B' i)) ∧
      (∀ i, Set.range (z' i).base ⊆
        ((pullback.fst c (specMap R (Localization.Away f)) ⁻¹ᵁ U : (pullback c (specMap R (Localization.Away f))).Opens) :
          Set ↥(pullback c (specMap R (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base)) ∧
      (∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M'), ¬ Smooth (pullback.snd (baseChange R c (Localization.Away f)) s) →
        (pullback.fst (baseChange R c (Localization.Away f)) s).base ⁻¹' Set.range (z' i).base ⊆
          (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))) := by sorry
