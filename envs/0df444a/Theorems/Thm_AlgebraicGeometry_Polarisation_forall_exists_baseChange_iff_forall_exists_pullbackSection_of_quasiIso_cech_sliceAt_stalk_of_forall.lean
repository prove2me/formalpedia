-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_forall_exists_baseChange_iff_forall_exists_pullbackSection_of_quasiIso_cech_sliceAt_stalk_of_forall
-- name    : AlgebraicGeometry.Polarisation.forall_exists_baseChange_iff_forall_exists_pullbackSection_of_quasiIso_cech_sliceAt_stalk_of_forall
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/7aa968d4-9384-5cb9-b43d-46204ec0ddbe
-- title:
--   Cocycle lifting over R/J' versus section lifting on the closed fibre
-- statement:
--   Setting. Let $K$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} K$ a morphism, $L$ a `RelativeGroupLaw` for $f$ (functorial multiplication, unit and inverse on $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$, with associativity, unit and inverse laws and naturality in $T$), and $hA$ an `AbelianSchemePropertyBundle` for $f$, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $g$ be a natural number, $f$ being smooth of relative dimension $g$. Let $M$ and $N$ be $\mathcal O_A$-modules, each invertible in the sense of `Scheme.Modules.IsInvertible` (every point has an open neighbourhood $U$ such that the restriction to $U$ is isomorphic to the unit module). Let $\mathcal K$ be an `OrderedAffineCover` of $A$: a finite linearly ordered index set $\mathcal K.\iota$ together with affine opens $\mathcal K.U_i$ whose supremum is $A$; it is assumed that $\#\mathcal K.\iota = g+1$. Finally let $y$ be a point of $A$.
--
--   Local model at $y$. Put $R = \mathcal O_{A,y}$, let $b_R : \operatorname{Spec} R \to A$ be the canonical morphism from the stalk, $t_R = b_R$ followed by $f$, and let $x_R$ be the $t_R$-point of $A$ given by $b_R$ (together with the identity $b_R \circ f = t_R$). Write $\pi : A \times_{\operatorname{Spec} K} \operatorname{Spec} R \to \operatorname{Spec} R$ for the second projection, and let
--   $$F_R = (\text{sliceAt } f\, x_R)^{*}\bigl(\Lambda(M) \otimes \mathrm{pr}_2^{*}N\bigr),$$
--   where $\Lambda(M) = \mathrm{mumfordBundle}\, f\, L\, M = \mathrm{add}^{*}M \otimes (\mathrm{pr}_1^{*}M^{\vee} \otimes \mathrm{pr}_2^{*}M^{\vee})$ on $A \times A$ (with $\mathrm{add}$ the addition morphism attached to $L$ and $M^\vee$ the internal dual), and $\mathrm{sliceAt}\, f\, x_R : A\times \operatorname{Spec} R \to A \times A$ is the morphism with components $\mathrm{pr}_1$ and $\mathrm{pr}_2$ followed by $b_R$. Let $\mathcal K_R$ be the ordered affine cover of $A \times \operatorname{Spec} R$ obtained by pulling back the opens of $\mathcal K$ along the first projection (affine, being a base change of an affine morphism), and let $G = \mathrm{ofModules}\,\pi\,F_R$ be the presheaf of $R$-modules $U \mapsto \Gamma(F_R, U)$ with its restriction maps, the $R$-structure coming from $\pi$. For an ordered affine cover $\mathcal C$, $\mathcal C.\mathrm{Idx}\,i$ denotes the strictly monotone maps $\mathrm{Fin}(i+1) \to \mathcal C.\iota$, $\mathcal C.\mathrm{inter}\,s$ the intersection of the corresponding opens, $G.\mathrm{cochain}\,\mathcal C\,i$ the module of families of sections over these intersections, and $G.d$ the Čech differential.
--
--   Quantified data. The assertion is made for all families $K^i$ ($i \in \mathbb N$) of finite free $R$-modules, all $R$-linear maps $\delta^i : K^i \to K^{i+1}$ with $\delta^{i+1} \circ \delta^i = 0$ and with $K^i$ subsingleton for $i > g$, all $R$-linear $\varphi^i : K^i \to G.\mathrm{cochain}\,\mathcal K_R\,i$ with $G.d\,i \circ \varphi^i = \varphi^{i+1} \circ \delta^i$, and all families $\Theta$ assigning to each commutative $R$-algebra $B$ and each $i$ a $B$-linear map from $B \otimes_R K^i$ to the degree-$i$ Čech cochains of the base-changed module on $(A\times\operatorname{Spec}R)\times_{\operatorname{Spec}R}\operatorname{Spec}B$ (pullback of $F_R$ along the first projection) with respect to the base-changed cover $\mathcal K_R.\mathrm{baseChange}\,\pi\,B$.
--
--   Hypothesis. The hypothesis on these data is the conjunction of: (a) a cohomology comparison, namely the existence of an $R$-linear isomorphism $\ker \delta^0 \cong G.H_0\,\mathcal K_R$ and, for every $i$, of an $R$-linear isomorphism $\ker \delta^{i+1}/(\operatorname{im}\delta^i \cap \ker \delta^{i+1}) \cong G.\mathrm{HSucc}\,\mathcal K_R\,i = \ker(G.d\,(i+1))/(\operatorname{im}(G.d\,i)\cap\ker(G.d\,(i+1)))$; and (b) for every commutative $R$-algebra $B$, six clauses: (b1) $\Theta_B$ is a chain map, $\Theta_B^{i+1}\circ(\delta^i\otimes B) = d^i \circ \Theta_B^i$ for the base-changed Čech differential; (b2) the pure-tensor formula $\Theta_B^i(a \otimes k)(s) = a \cdot \mathrm{res}(\varphi^i(k)(s))$, where $\varphi^i(k)(s)$ is carried by the unit of the pullback–pushforward adjunction along the first projection, at $F_R$ and at the open $\mathcal K_R.\mathrm{inter}\,s$, and then restricted along the inclusion $\mathcal K_R.\mathrm{baseChange\_inter\_le}\,\pi\,B\,s$; (b3) in degree $0$, any $x \in B\otimes K^0$ with $(\delta^0\otimes B)(x)=0$ and $\Theta_B^0(x)=0$ vanishes; (b4) every degree-$0$ Čech cocycle is $\Theta_B^0(x)$ for some $x$ with $(\delta^0\otimes B)(x)=0$; (b5) for every $i$ and every $x \in B \otimes K^{i+1}$ with $(\delta^{i+1}\otimes B)(x)=0$, if $\Theta_B^{i+1}(x)$ lies in the image of $d^i$ then $x$ lies in the image of $\delta^i \otimes B$; (b6) for every $i$, every Čech cocycle $y$ in degree $i+1$ agrees, modulo the image of $d^i$, with $\Theta_B^{i+1}(x)$ for some $x \in B \otimes K^{i+1}$ killed by $\delta^{i+1}\otimes B$.
--
--   Conclusion. Under this hypothesis, for every ideal $J' \subseteq \mathfrak m = \mathfrak m_R$ containing some power $\mathfrak m^n$, the following holds. Put $X = A \times_{\operatorname{Spec}K}\operatorname{Spec}R$, $B = R/J'$, $k = R/\mathfrak m$, $X_B = X \times_{\operatorname{Spec}R}\operatorname{Spec}B$, $X_k = X \times_{\operatorname{Spec}R}\operatorname{Spec}k$, and let $F_B$, $F_k$ be the pullbacks of $F_R$ along the respective first projections. Let $u : B \to k$ be the quotient factorisation through $J' \subseteq \mathfrak m$, so that $\operatorname{Spec}k \to \operatorname{Spec}R$ factors as $\operatorname{Spec}(u)$ followed by $\operatorname{Spec}B \to \operatorname{Spec}R$, let $gq : X_k \to X_B$ be the morphism induced by the first projection of $X_k$ and by its second projection followed by $\operatorname{Spec}(u)$, and let $e : gq^{*}F_B \cong F_k$ be the canonical identification obtained from the composition-of-pullbacks isomorphism and the compatibility of $gq$ with the first projections. Then the two following statements are equivalent:
--
--   (i) every $z \in k \otimes_R K^0$ with $(\delta^0\otimes k)(z) = 0$ is the image of some $w \in B \otimes_R K^0$ with $(\delta^0 \otimes B)(w) = 0$ under the map $B \otimes_R K^0 \to k \otimes_R K^0$ induced by $B \to k$;
--
--   (ii) for every morphism $s_k : \mathcal O_{X_k} \to F_k$ of $\mathcal O_{X_k}$-modules there is a morphism $s : \mathcal O_{X_B} \to F_B$ such that `pullbackSection` of $s$ along $gq$ (that is, the inverse of the canonical isomorphism $gq^{*}\mathcal O_{X_B} \cong \mathcal O_{X_k}$ followed by $gq^{*}s$) followed by $e$ equals $s_k$.
--
--   This is the bridge between the linear-algebra side and the geometric side of the cohomology-and-base-change argument for the Mumford bundle slice over the local ring at a point: liftability of degree-zero cocycles of the finite free model complex along $R/J' \to R/\mathfrak m$ is equivalent to liftability of global sections of the slice from the closed fibre $X_k$ to $X_B$. It is used in [`AlgebraicGeometry.Polarisation.exists_free_complex_cech_sliceAt_stalk_and_seesaw`](thm.html#AlgebraicGeometry.Polarisation.exists_free_complex_cech_sliceAt_stalk_and_seesaw), where the free complex and the seesaw-type conclusion are produced together.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_forall_exists_baseChange_iff_forall_exists_pullbackSection_of_quasiIso_cech_sliceAt_stalk_of_forall.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

open TensorProduct in

theorem AlgebraicGeometry.Polarisation.forall_exists_baseChange_iff_forall_exists_pullbackSection_of_quasiIso_cech_sliceAt_stalk_of_forall
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y : A) :
    letI R : Type := ↥(A.presheaf.stalk y)
    letI bR : Spec (CommRingCat.of R) ⟶ A := A.fromSpecStalk y
    letI tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) := bR ≫ f
    letI xR : SchemeHomOver tR f := ⟨bR, rfl⟩
    letI π : pullback f tR ⟶ Spec (CommRingCat.of R) := pullback.snd f tR
    letI FR : (pullback f tR).Modules :=
      (Scheme.Modules.pullback (sliceAt f xR)).obj
        (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tR) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒦R : (pullback f tR).OrderedAffineCover := 𝒦.comap (pullback.fst f tR)
    letI G := OModulePresheaf.ofModules π FR
        ∀ (Kc : ℕ → Type) [∀ i, AddCommGroup (Kc i)] [∀ i, Module R (Kc i)]
        [∀ i, Module.Finite R (Kc i)] [∀ i, Module.Free R (Kc i)]
        (δ : ∀ i, Kc i →ₗ[R] Kc (i + 1)) (_ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (_ : ∀ i, g < i → Subsingleton (Kc i))
        (φ : ∀ i, Kc i →ₗ[R] (OModulePresheaf.ofModules π FR).cochain 𝒦R i)
        (_ : ∀ i, (OModulePresheaf.ofModules π FR).d 𝒦R i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
        (Θ : ∀ (B : Type) [CommRing B] [Algebra R B] (i : ℕ), B ⊗[R] Kc i →ₗ[B]
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).cochain (𝒦R.baseChange π B) i),
        (((Nonempty (LinearMap.ker (δ 0) ≃ₗ[R] G.H0 𝒦R) ∧
          ∀ i : ℕ, Nonempty
            ((LinearMap.ker (δ (i + 1)) ⧸ (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) ≃ₗ[R]
              G.HSucc 𝒦R i)) ∧
        ∀ (B : Type) [CommRing B] [Algebra R B],
          (∀ i : ℕ, Θ B (i + 1) ∘ₗ (δ i).baseChange B
            = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) i
              ∘ₗ Θ B i) ∧
          (∀ (i : ℕ) (a : B) (k : Kc i) (s : 𝒦R.Idx i),
            Θ B i (a ⊗ₜ[R] k) s
              = a • (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                  ((Scheme.Modules.pullback
                    (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).res
                  (𝒦R.baseChange_inter_le π B s)
                  ((((Scheme.Modules.pullbackPushforwardAdjunction
                    (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).unit.app FR).app
                    (𝒦R.inter s)).hom (φ i k s))) ∧
          (∀ x : B ⊗[R] Kc 0, (δ 0).baseChange B x = 0 → Θ B 0 x = 0 → x = 0) ∧
          (∀ y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).cochain (𝒦R.baseChange π B) 0,
            (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) 0 y = 0 →
            ∃ x : B ⊗[R] Kc 0, (δ 0).baseChange B x = 0 ∧ Θ B 0 x = y) ∧
          (∀ (i : ℕ) (x : B ⊗[R] Kc (i + 1)), (δ (i + 1)).baseChange B x = 0 →
            Θ B (i + 1) x ∈ LinearMap.range
              ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) i) →
            x ∈ LinearMap.range ((δ i).baseChange B)) ∧
          (∀ (i : ℕ) (y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).cochain (𝒦R.baseChange π B) (i + 1)),
            (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) (i + 1) y = 0 →
            ∃ x : B ⊗[R] Kc (i + 1), (δ (i + 1)).baseChange B x = 0 ∧
              Θ B (i + 1) x - y ∈ LinearMap.range
                ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                  ((Scheme.Modules.pullback
                    (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) i)))) →
      ∀ (J' : Ideal R) (hJ' : J' ≤ IsLocalRing.maximalIdeal R), (∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ J') →
        letI X := pullback f tR
        letI B : Type := R ⧸ J'
        letI kk : Type := R ⧸ IsLocalRing.maximalIdeal R
        letI XB := pullback π (Scheme.TwoAffineOpenCover.specMap R B)
        letI Xk := pullback π (Scheme.TwoAffineOpenCover.specMap R kk)
        letI FB : XB.Modules := (Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR
        letI Fk : Xk.Modules := (Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R kk))).obj FR
        letI u : B →+* kk := Ideal.Quotient.factor hJ'
        letI hfac : Scheme.TwoAffineOpenCover.specMap R kk =
            Spec.map (CommRingCat.ofHom u) ≫ Scheme.TwoAffineOpenCover.specMap R B := by
          rw [Scheme.TwoAffineOpenCover.specMap, Scheme.TwoAffineOpenCover.specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2
        letI gq : Xk ⟶ XB := pullback.lift (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R kk))
            (pullback.snd π (Scheme.TwoAffineOpenCover.specMap R kk) ≫ Spec.map (CommRingCat.ofHom u))
            (by rw [pullback.condition, Category.assoc, ← hfac])
        letI e : (Scheme.Modules.pullback gq).obj FB ≅ Fk :=
          (Scheme.Modules.pullbackComp gq (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).app FR ≪≫
            (Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _)).app FR
        ((∀ z : kk ⊗[R] Kc 0, (δ 0).baseChange kk z = 0 →
            ∃ w : B ⊗[R] Kc 0, (δ 0).baseChange B w = 0 ∧ LinearMap.rTensor (Kc 0) (Submodule.factor hJ') w = z) ↔
          (∀ sk : 𝟙_ Xk.Modules ⟶ Fk, ∃ s : 𝟙_ XB.Modules ⟶ FB, Scheme.Modules.pullbackSection gq s ≫ e.hom = sk)) := by sorry
