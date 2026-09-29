-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_charts_forall_locIso_of_forall_iso_localizationAway_of_three_le
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_charts_forall_locIso_of_forall_iso_localizationAway_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/55dc5424-b595-54b1-872b-c02b0e4e24ff
-- title:
--   Glued charts for polarised abelian schemes over Spec S
-- statement:
--   Fix naturals $g,d,n$ with $3 \le n$, a commutative ring $S$ (in the zero universe) in which $n$ is a unit, and elements $r_0,\dots,r_{k-1}$ of $S$ spanning the unit ideal, together with rings $B_i$ that are $S$-algebras realising the localisation of $S$ away from $r_i$. For each $i$ let $u_i$ be a polarised abelian scheme of type $(g,d,n)$ over $B_i$: a scheme $(u_i).A$ with a structure morphism to $\operatorname{Spec} B_i$ which is smooth, proper with connected fibres, carries a commutative relative group law on $T$-points with all fibres of topological Krull dimension $g$, together with $2g$ sections $P_m$ killed by $n$ that are independent and generate the $n$-torsion on geometric fibres, and an invertible module $(u_i).\mathrm{pol}$ admitting a projective presentation whose associated morphism is a closed immersion and having geometric fibre $H^0$-rank $d$. Assume the overlap hypothesis: for all $i,j$, every ring $C$ realising the localisation of $S$ away from $r_i r_j$, all $S$-algebra maps $\rho_1 : B_i \to C$, $\rho_2 : B_j \to C$ and all $v_1,v_2$ of type $(g,d,n)$ over $C$ which are pullbacks of $u_i$ along $\rho_1$ resp. of $u_j$ along $\rho_2$ (cartesian square, compatibility of the group law on $T$-points, the level sections pulled back, and an isomorphism of the pulled-back polarisation), the objects $v_1$ and $v_2$ are isomorphic in the sense of the project's `Iso`: an isomorphism of schemes over $\operatorname{Spec} C$ compatible with the group laws and with the level sections, whose effect on the polarisations is an isomorphism after restriction over some open neighbourhood of each point of $\operatorname{Spec} C$. The conclusion asserts the existence of a scheme $Y$, a morphism $f : Y \to \operatorname{Spec} S$ and morphisms $\iota_i : (u_i).A \to Y$ such that: each $\iota_i$ is an open immersion; each square formed by $\iota_i$, $(u_i).f$, $f$ and $\operatorname{Spec}$ of $S \to B_i$ is cartesian; every point of $Y$ lies in the image of some $\iota_i$; for all $i,j$, every $C$ as above with maps $\rho_1,\rho_2$, and every $m < 2g$, the composite of $\operatorname{Spec}\rho_1$ with $(u_i).P_m$ and $\iota_i$ equals that of $\operatorname{Spec}\rho_2$ with $(u_j).P_m$ and $\iota_j$; the group laws glue, in the sense that for all $i,j$, any scheme $T$ with morphisms $t_i \to \operatorname{Spec} B_i$, $t_j \to \operatorname{Spec} B_j$, and points $a,b$ of $(u_i).A$ over $t_i$ and $a',b'$ of $(u_j).A$ over $t_j$ with $a$ followed by $\iota_i$ equal to $a'$ followed by $\iota_j$ and likewise for $b,b'$, the product of $a,b$ for $(u_i).L$ followed by $\iota_i$ agrees with the product of $a',b'$ for $(u_j).L$ followed by $\iota_j$; and the polarisations agree locally on the base, namely for all $i,j$ and every point $q$ of the fibre product of $\iota_i$ and $\iota_j$ there is an open $U \subseteq \operatorname{Spec} S$ containing the image of $q$ under the first projection followed by $\iota_i$ and $f$, such that the restrictions to the preimage of $U$ of the two pullbacks of $(u_i).\mathrm{pol}$ and $(u_j).\mathrm{pol}$ along the two projections are isomorphic.
--
--   This is the Zariski-gluing step for polarised abelian schemes with full level-$n$ structure: from objects over the standard affine cover $\operatorname{Spec} B_i$ of $\operatorname{Spec} S$ that agree on overlaps, one produces a single scheme over $\operatorname{Spec} S$ carrying the $u_i$ as charts, with the group laws, level sections and (locally on the base) polarisations matching on overlaps. It feeds the subsequent statement that the glued object is itself a polarised abelian scheme over $S$ whose base changes recover the $u_i$, used in the rigidity/representability input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_charts_forall_locIso_of_forall_iso_localizationAway_of_three_le.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_charts_forall_locIso_of_forall_iso_localizationAway_of_three_le
    {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    (u : ∀ i, PolarisedAbelianScheme g d n (B i))
    (hover : ∀ (i j : Fin k) (C : Type) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
          (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C) (v₁ v₂ : PolarisedAbelianScheme g d n C),
          PolarisedAbelianScheme.IsPullback ρ₁.toRingHom (u i) v₁ →
          PolarisedAbelianScheme.IsPullback ρ₂.toRingHom (u j) v₂ →
          PolarisedAbelianScheme.Iso v₁ v₂) :
    ∃ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)) (ι : ∀ i, (u i).A ⟶ Y),
      (∀ i, IsOpenImmersion (ι i)) ∧
      (∀ i, CategoryTheory.IsPullback (ι i) (u i).f f (Spec.map (CommRingCat.ofHom (algebraMap S (B i))))) ∧
      (∀ y : ↥Y, ∃ (i : Fin k) (x : ↥(u i).A), (ι i).base x = y) ∧

      (∀ (i j : Fin k) (C : Type) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
          (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C) (m : Fin (2 * g)),
          Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ ((u i).P m).1 ≫ ι i =
            Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ ((u j).P m).1 ≫ ι j) ∧

      (∀ (i j : Fin k) {T : Scheme.{0}} (tᵢ : T ⟶ Spec (CommRingCat.of (B i))) (tⱼ : T ⟶ Spec (CommRingCat.of (B j)))
          (a b : SchemeHomOver tᵢ (u i).f) (a' b' : SchemeHomOver tⱼ (u j).f),
          a.1 ≫ ι i = a'.1 ≫ ι j → b.1 ≫ ι i = b'.1 ≫ ι j →
            ((u i).L.mul tᵢ a b).1 ≫ ι i = ((u j).L.mul tⱼ a' b').1 ≫ ι j) ∧

      (∀ (i j : Fin k) (q : ↥(pullback (ι i) (ι j))), ∃ U : (Spec (CommRingCat.of S)).Opens,
          (pullback.fst (ι i) (ι j) ≫ ι i ≫ f).base q ∈ U ∧
          Nonempty
            ((Scheme.Modules.pullback ((pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ⁻¹ᵁ U).ι).obj
                ((Scheme.Modules.pullback (pullback.fst (ι i) (ι j))).obj (u i).pol) ≅
              (Scheme.Modules.pullback ((pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ⁻¹ᵁ U).ι).obj
                ((Scheme.Modules.pullback (pullback.snd (ι i) (ι j))).obj (u j).pol))) := by sorry
