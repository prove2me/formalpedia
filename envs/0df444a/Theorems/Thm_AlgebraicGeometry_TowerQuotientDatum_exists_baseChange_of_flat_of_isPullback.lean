-- Prove2me | Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_exists_baseChange_of_flat_of_isPullback
-- name    : AlgebraicGeometry.TowerQuotientDatum.exists_baseChange_of_flat_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/fa3df810-e307-59c4-b839-ab937dcb1dec
-- title:
--   Flat base change of a tower quotient datum
-- statement:
--   Let $\mathcal O$ be a domain which is a discrete valuation ring, $\pi$ an irreducible element of $\mathcal O$, and assume $\mathcal O$ is adically complete for $(\pi)$. Let $X_n$ be schemes with structure morphisms $xb_n : X_n \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$ and transitions $xt_n : X_n \to X_{n+1}$ such that each square formed by $xt_n$, $xb_n$, $xb_{n+1}$ and $\operatorname{Spec}$ of the reduction $\mathcal O/\pi^{n+2} \to \mathcal O/\pi^{n+1}$ is cartesian, each $xb_n$ is proper and flat, and every finite set of points of $X_n$ lies in an affine open. Let $G$ be a finite group acting by automorphisms $a_n : G \to \operatorname{Aut}(X_n)$ over the base and compatibly with the $xt_n$, and let $D$ be a `TowerQuotientDatum` for these data: a tower $Y_n \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$ with cartesian transitions $yt_n$ and proper flat structure maps, together with morphisms $p_n : X_n \to Y_n$ over the base, compatible with the transitions and making the squares $(xt_n, p_n, p_{n+1}, yt_n)$ cartesian, which are $G$-invariant, finite, surjective, remain epimorphisms after restriction over every open of $Y_n$, and satisfy a local universal property for $G$-invariant families of morphisms out of the preimages $p_n^{-1}(U_n)$ of compatible systems of opens $U_n \subseteq Y_n$, plus the remaining axioms of the structure. Let $S$ be a commutative flat $\mathcal O$-algebra and write $\pi_S$ for the image of $\pi$. Let $X'_n \to \operatorname{Spec}(S/\pi_S^{n+1})$ be a second tower with transitions $xt'_n$ cartesian over $\operatorname{Spec}(S/\pi_S^{n+1}) \to \operatorname{Spec}(S/\pi_S^{n+2})$, an action $a'_n : G \to \operatorname{Aut}(X'_n)$ over the base, and morphisms $q_n : X'_n \to X_n$ which are $G$-equivariant, compatible with the transitions, and exhibit $X'_n$ as the base change $X_n \times_{\operatorname{Spec}(\mathcal O/\pi^{n+1})} \operatorname{Spec}(S/\pi_S^{n+1})$. Then there exist a `TowerQuotientDatum` $D'$ for $(S, \pi_S, X', xb', xt', G, a')$ and morphisms $r_n : D'.Y_n \to D.Y_n$ such that each square formed by $r_n$, $D'.yb_n$, $D.yb_n$ and $\operatorname{Spec}$ of $\mathcal O/\pi^{n+1} \to S/\pi_S^{n+1}$ is cartesian, $D'.p_n$ followed by $r_n$ equals $q_n$ followed by $D.p_n$, and $D'.yt_n$ followed by $r_{n+1}$ equals $r_n$ followed by $D.yt_n$.
--
--   This is the flat base change statement for quotients of a $\pi$-adic tower of proper flat schemes by a finite group: the quotient datum of the base-changed tower exists and its levels are the base changes of the original quotient, compatibly with the quotient maps and the transitions. It is invoked in the Čerednik–Drinfeld part of the development, where the quotient tower constructed over $\mathcal O$ is transported to a flat extension of the base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TowerQuotientDatum_exists_baseChange_of_flat_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.TowerQuotientDatum.exists_baseChange_of_flat_of_isPullback
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (haff : ∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n)))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))
    (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)

    (S : Type) [CommRing S] [Algebra 𝒪 S] [Module.Flat 𝒪 S]
    (X' : ℕ → Scheme.{0}) (xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
    (xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1)) (a' : ∀ n : ℕ, G →* Aut (X' n))
    (q : ∀ n : ℕ, X' n ⟶ X n)
    (hq : ∀ n : ℕ, IsPullback (q n) (xb' n) (xb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hcart' : ∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1))))))))
    (hq_xt : ∀ n : ℕ, xt' n ≫ q (n + 1) = q n ≫ xt n)
    (hq_a : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ q n = q n ≫ (a n g).hom)
    (ha'_over : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ xb' n = xb' n) :
    ∃ (D' : TowerQuotientDatum S (algebraMap 𝒪 S π) X' xb' xt' G a') (r : ∀ n : ℕ, D'.Y n ⟶ D.Y n),
      (∀ n : ℕ, IsPullback (r n) (D'.yb n) (D.yb n)
        (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))) ∧
      (∀ n : ℕ, D'.p n ≫ r n = q n ≫ D.p n) ∧
      (∀ n : ℕ, D'.yt n ≫ r (n + 1) = r n ≫ D.yt n) := by sorry
