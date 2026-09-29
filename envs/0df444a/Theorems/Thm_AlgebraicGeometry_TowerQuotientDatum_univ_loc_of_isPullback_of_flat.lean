-- Prove2me | Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_univ_loc_of_isPullback_of_flat
-- name    : AlgebraicGeometry.TowerQuotientDatum.univ_loc_of_isPullback_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/82aed67f-24ea-5f12-a15f-8bf2f3cf0a5a
-- title:
--   Local universal property under flat base change of a tower quotient
-- statement:
--   Let $\mathcal O$ be a domain which is a discrete valuation ring, $\pi$ an irreducible element, and suppose $\mathcal O$ is $(\pi)$-adically complete. Let $X_n$ be schemes with structure morphisms $xb_n : X_n \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$ and transitions $xt_n : X_n \to X_{n+1}$ making each square over $\mathcal O/\pi^{n+2} \to \mathcal O/\pi^{n+1}$ cartesian, with every $xb_n$ proper and flat, and assume every finite subset of $X_n$ lies in an affine open. Let $G$ be a finite group acting on each $X_n$ by automorphisms over the base and compatibly with the transitions, and let $D$ be a tower quotient datum: schemes $Y_n$ with proper flat $yb_n : Y_n \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$, cartesian transitions $yt_n$, and morphisms $p_n : X_n \to Y_n$ over the base, compatible with the transitions and cartesian over $yt_n$, $G$-invariant, finite, surjective, with $p_n|_U$ epi for every open $U \subseteq Y_n$, and satisfying the local universal property for $G$-invariant transition-compatible families. Let $S$ be a flat $\mathcal O$-algebra, $X'_n \to \operatorname{Spec}(S/(\pi_S)^{n+1})$ a tower with $G$-action, transitions $xt'_n$ and $q_n : X'_n \to X_n$ exhibiting $X'_n$ as the base change of $X_n$ along $\mathcal O/\pi^{n+1} \to S/(\pi_S)^{n+1}$, with the transition squares cartesian and $q_n$ compatible with transitions and the actions. Let $Y'_n$, $yb'_n$, $yt'_n$, $p'_n : X'_n \to Y'_n$ and $r_n : Y'_n \to D.Y_n$ be data exhibiting $Y'_n$ as the base change of $D.Y_n$ and $X'_n$ as $X_n \times_{Y_n} Y'_n$ (via $q_n$, $p'_n$, $D.p_n$, $r_n$), with $yt'_n r_{n+1} = r_n (D.yt_n)$, both legs of $yt'_n$ and of $p'_n$ pinned over the base, $p'_n$ $G$-invariant and compatible with the transitions. Then for every scheme $T$, every family of opens $U_n \subseteq Y'_n$ with $(yt'_n)^{-1}(U_{n+1}) = U_n$, and every family of morphisms $u_n : (p'_n)^{-1}(U_n) \to T$ that is invariant under the restrictions of the $G$-action and compatible with the restrictions of the transitions $xt'_n$, there exist morphisms $v_n : U_n \to T$ with $u_n$ equal to the restriction $(p'_n)|_{U_n}$ followed by $v_n$. No uniqueness of $v$ is asserted.
--
--   This is exactly the `univ_loc` field required to construct the flat base change of a tower quotient datum along $\mathcal O \to S$, the remaining fields of that base change being formal consequences of pullback pasting and stability of properness, flatness, finiteness and surjectivity. It is used by [`AlgebraicGeometry.TowerQuotientDatum.exists_baseChange_of_flat_of_isPullback`](thm.html#AlgebraicGeometry.TowerQuotientDatum.exists_baseChange_of_flat_of_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TowerQuotientDatum_univ_loc_of_isPullback_of_flat.lean

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.TowerQuotientDatum.univ_loc_of_isPullback_of_flat
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
    (ha'_over : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ xb' n = xb' n)

    (Y' : ℕ → Scheme.{0})
    (yb' : ∀ n : ℕ, Y' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
    (yt' : ∀ n : ℕ, Y' n ⟶ Y' (n + 1)) (p' : ∀ n : ℕ, X' n ⟶ Y' n) (r : ∀ n : ℕ, Y' n ⟶ D.Y n)
    (hbase : ∀ n : ℕ, IsPullback (r n) (yb' n) (D.yb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hsq : ∀ n : ℕ, IsPullback (q n) (p' n) (D.p n) (r n))
    (hyt'r : ∀ n : ℕ, yt' n ≫ r (n + 1) = r n ≫ D.yt n)
    (hyt'b : ∀ n : ℕ, yt' n ≫ yb' (n + 1) = yb' n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1)))))))
    (hp'_over : ∀ n : ℕ, p' n ≫ yb' n = xb' n)
    (hp'_inv : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ p' n = p' n)
    (hp'_xt : ∀ n : ℕ, xt' n ≫ p' (n + 1) = p' n ≫ yt' n) :
    ∀ (T : Scheme.{0}) (U : ∀ n : ℕ, (Y' n).Opens) (hU : ∀ n : ℕ, (yt' n) ⁻¹ᵁ (U (n + 1)) = U n)
      (u : ∀ n : ℕ, (↑((p' n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T),
      (∀ (n : ℕ) (g : G),
        Scheme.Hom.resLE (a' n g).hom ((p' n) ⁻¹ᵁ (U n)) ((p' n) ⁻¹ᵁ (U n))
          (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) ≫ u n = u n) →
      (∀ n : ℕ,
        Scheme.Hom.resLE (xt' n) ((p' (n + 1)) ⁻¹ᵁ (U (n + 1))) ((p' n) ⁻¹ᵁ (U n))
          (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hU]) ≫ u (n + 1) = u n) →
      ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ T, ∀ n : ℕ, (p' n) ∣_ (U n) ≫ v n = u n := by sorry
