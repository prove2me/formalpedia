-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_one_cochain_isTangentCoordsOfPairAtVia_pin_of_local_lifts_hom
-- name    : AlgebraicGeometry.SmallExtension.exists_one_cochain_isTangentCoordsOfPairAtVia_pin_of_local_lifts_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/79b67cc6-3250-5e0e-ae53-5ef63b10ad1c
-- title:
--   Naturality 1-cochain of tangent coordinates along a morphism
-- statement:
--   Throughout, $k$ denotes the residue field `ResidueField T'` of $T'$, and $I=\ker\pi$. For an ordered affine cover $\mathcal K$ of a scheme, $\mathcal K.\mathrm{Idx}\,n$ is the set of strictly monotone maps $\mathrm{Fin}(n+1)\to\mathcal K.\iota$ and $\mathcal K.\mathrm{inter}\,s=\bigsqcap_j \mathcal K.U(s_j)$; `(OModulePresheaf.unit f).cochain K n` is the module of families indexed by $s\in\mathcal K.\mathrm{Idx}\,n$ of sections of the structure sheaf over $\mathcal K.\mathrm{inter}\,s$.
--
--   **Small extension data.** $T'$ is a commutative local Artinian ring, $T$ a commutative ring, and $\pi:T'\to T$ a ring homomorphism that is surjective (`hπ`), has nilpotent kernel (`hker`), satisfies $(\ker\pi)\cdot\mathfrak m_{T'}=0$ (`hsmall`) and $\ker\pi\subseteq\mathfrak m_{T'}$ (`hI`); $\rho:T\to k$ is a ring homomorphism with $\rho\circ\pi$ the residue map of $T'$ (`hρ`). $V$ is a finite-dimensional $k$-vector space equipped in addition with a $T'$-module structure compatible with the $k$-structure and with a central right $k$-action, and $\iota:V\to T'$ is an injective $T'$-linear map (`hι`) whose range is exactly $\ker\pi$ as a $T'$-submodule (`hιI`).
--
--   **The $A$-side base, cover and local lifts.** $f_0:A_0\to\operatorname{Spec}T$ is separated and smooth, $\mathcal U$ is an ordered affine cover of $A_0$ (a finite linearly ordered index set $\mathcal U.\iota$ and affine opens $\mathcal U.U\,a$ with supremum $\top$). For each $a$ there are a scheme $Y\,a$, a morphism $q\,a:Y\,a\to\operatorname{Spec}T'$ which is smooth (`hq`), and $g\,a:\mathcal U.U\,a\to Y\,a$ such that the square formed by $g\,a$, the composite of the inclusion of $\mathcal U.U\,a$ with $f_0$, $q\,a$ and $\operatorname{Spec}\pi$ is cartesian (`hg`); thus $Y\,a$ is a smooth lift of $\mathcal U.U\,a$ along $\pi$.
--
--   **The $A$-side special fibre.** $f_k:A_k\to\operatorname{Spec}k$ is separated, $L_k$ is a relative group law on $f_k$ (functorial multiplication, unit and inverse on morphisms over $\operatorname{Spec}k$, with associativity, unit and inverse laws and naturality in the base), $i_0:A_k\to A_0$ is an affine morphism whose square with $f_k$, $f_0$ and $\operatorname{Spec}\rho$ is cartesian (`hi₀`), $U_e$ is an affine open of $A_k$ (`hUe`), and $e_1:\operatorname{Spec}k\to U_e$ satisfies that $e_1$ followed by the inclusion of $U_e$ is the unit section $L_k.\mathrm{one}(\mathrm{id})$ (`he₁`).
--
--   **The $A$-side open-transport family.** $O$ assigns to each index $a$ and each open $W\subseteq A_0$ an open $O\,a\,W\subseteq Y\,a$, subject to: $g\,a^{-1}(O\,a\,W)$ is the preimage of $W$ in $\mathcal U.U\,a$ (`hO`); monotonicity in $W$ (`hOm`); $O\,a(\mathcal U.U\,a)=\top$ (`hOtop`); $O\,a\,W\sqcap O\,a\,W'\le O\,a(W\sqcap W')$ (`hOinf`); and $O\,a\,W$ is affine whenever $W$ is affine and $W\le\mathcal U.U\,a$ (`hOaff`).
--
--   **The $A$-side chart comparisons.** For every $n$ and every $s\in\mathcal U.\mathrm{Idx}\,n$, $\sigma\,s$ is a ring isomorphism from $k\otimes_{T'}\Gamma(Y(s_0),O(s_0)(\mathcal U.\mathrm{inter}\,s))$ onto $\Gamma(A_k,(\mathcal U.\mathrm{comap}\,i_0).\mathrm{inter}\,s)$, where the sections of $Y(s_0)$ are a $T'$-algebra via $q(s_0)$. The hypothesis `hσ₁` identifies $\sigma\,s$ geometrically: the composite of the `isoSpec` of the intersection on $A_k$, $\operatorname{Spec}$ of $\sigma\,s$, $\operatorname{Spec}$ of the right inclusion into the tensor product, and the `fromSpec` of $O(s_0)(\mathcal U.\mathrm{inter}\,s)$ equals the composite of the open immersions on $A_k$, the restriction of $i_0$, the open immersion on $A_0$ and $g(s_0)$. The hypothesis `hσ₂` says $\sigma\,s(x\otimes 1)$ is the image of $x\in k$ under the structure map of $\Gamma(A_k,(\mathcal U.\mathrm{comap}\,i_0).\mathrm{inter}\,s)$ coming from $f_k$.
--
--   **The $A$-side transitions.** For $a<b$, $\varphi\,a\,b$ is an isomorphism $O\,a(\mathcal U.U\,a\sqcap\mathcal U.U\,b)\cong O\,b(\mathcal U.U\,a\sqcap\mathcal U.U\,b)$ lying over $\operatorname{Spec}T'$ (`hφq`), compatible with the two local lifts in the sense that the lifts $\gamma,\gamma'$ of the overlap into the two charts exist and satisfy $\gamma$ followed by $\varphi\,a\,b$ equals $\gamma'$ (`hφg`), and matching the $O$-families on preimages (`hφO`). For each triple $r\in\mathcal U.\mathrm{Idx}\,2$ there are isomorphisms $\rho^{ab}_r,\rho^{bc}_r,\rho^{ac}_r$ between the corresponding charts over the triple intersection, pinned to the $\varphi$'s by the commutation relations `hρab`, `hρbc`, `hρac` with the restriction morphisms of the $O$-families.
--
--   **The $A$-side degree-two datum.** $\omega$ lies in [`Algebra.PointDerivations`](def/Algebra_PointDerivations.html#L9) $k$ $\Gamma(A_k,U_e)$ $\mathrm{ev}$ $M$, that is, $\omega$ is a $k$-linear map $\Gamma(A_k,U_e)\to M$ with $\omega(ab)=\mathrm{ev}(a)\,\omega(b)+\mathrm{ev}(b)\,\omega(a)$, where $\mathrm{ev}$ is evaluation at $e_1$ (the composite of the inverse of the top isomorphism of $U_e$, the map on global sections induced by $e_1$ and the $\Gamma$–$\operatorname{Spec}$ isomorphism), and $M$ is the module of $k$-linear maps from the dual $V^\vee$ to the degree-two Čech cochains of the structure sheaf for the cover $\mathcal U.\mathrm{comap}\,i_0$ of $A_k$. The hypothesis `hω` states that for each triple $r$, writing $C_r=\Gamma(Y(r_0),O(r_0)(\mathcal U.\mathrm{inter}\,r))$ as a $T'$-algebra via $q(r_0)$, there is $cs:\Gamma(A_k,U_e)\to\operatorname{Hom}_k(V^\vee,k\otimes_{T'}C_r)$ which is a system of tangent coordinates of the pair $(u,v)$ at the point datum, where $u$ is the inverse of the `isoSpec` of $O(r_0)(\mathcal U.\mathrm{inter}\,r)$ followed by $\rho^{ac}_r$ and the inclusion of $O(r_2)(\mathcal U.\mathrm{inter}\,r)$ into $Y(r_2)$, and $v$ is the same `isoSpec` inverse followed by $\rho^{ab}_r$, $\rho^{bc}_r$ and that inclusion, the point datum being $f_k$, $L_k$, the open $i_0^{-1}(\mathcal U.U(r_2))$ with the morphism given by the restriction of $i_0$ followed by $g(r_2)$, and the chart $U_e$; moreover $\sigma\,r(cs\,a\,\xi)=\omega(a)(\xi)(r)$ for all $a$ and $\xi$. Here the predicate `IsTangentCoordsOfPairAtVia` $I$ $V$ $\iota$ $C$ $u$ $v$ $x_k$ $L_k$ $W$ $a_W$ $U_e$ $c$ asserts the existence of a morphism $w_0$ from $\operatorname{Spec}$ of the thickening $(k\otimes_{T'}C)\otimes_k(k\oplus V)$ (trivial square-zero extension) to $W$ lying over the tangent base map, and a morphism $w_1$ from the same source to $U_e$, such that: $w_0$ followed by $a_W$ is a tangent vector of the pair $(u,v)$, meaning there are a ring homomorphism $\vartheta$ from `pairRing` $I$ $C$ to the thickening satisfying the predicate `IsSchlessingerMap` $I$ $V$ $\iota$ $C$ and a morphism $\phi$ from $\operatorname{Spec}$ of `pairRing` $I$ $C$ to the target which pulls back along `pairFst` and `pairSnd` to $u$ and $v$ respectively and with $w_0$ followed by $a_W$ equal to $\operatorname{Spec}\vartheta$ followed by $\phi$; $w_1$ followed by the inclusion of $U_e$ is the translate of $w_0$ to the unit of the group law (`RelTangentPoints.translate`); and $c$ is the tangent-coordinate function `tangentCoords` of the ring homomorphism $\Gamma(A_k,U_e)\to$ thickening induced by $w_1$. Finally `hωZ` says that for all $a$ and $\xi$ the Čech differential in degree two of $\omega(a)(\xi)$ vanishes.
--
--   **The $X$-side.** The same data are given for a second separated smooth $f_{X_0}:X_0\to\operatorname{Spec}T$: an ordered affine cover $\mathcal V$, charts $Z$ with smooth structure morphisms $q_Z$ (`hqZ`) and lifts $g_Z$ with cartesian squares (`hgZ`); a separated $f_{X_k}:X_k\to\operatorname{Spec}k$ with relative group law $L_X$, an affine morphism $j_0$ with cartesian square over $\operatorname{Spec}\rho$ (`hj₀`), an affine open $U^X_e$ (`hUXe`) with a point $e^X_1$ over the unit section (`heX₁`); an open-transport family $O_X$ with the five conditions `hOX`, `hOXm`, `hOXtop`, `hOXinf`, `hOXaff`; chart comparisons $\sigma_X$ with `hσX₁` and `hσX₂`; transitions $\varphi_X$ with `hφXq`, `hφXg`, `hφXO`; triple transitions $\rho^{ab}_X,\rho^{bc}_X,\rho^{ac}_X$ pinned by `hρXab`, `hρXbc`, `hρXac`; and a point derivation $\omega_X$ with the degree-two tangent-coordinate property `hωX` and the cocycle condition `hωXZ`, all of exactly the shape described on the $A$-side.
--
--   **The morphism data.** $h_0:X_0\to A_0$ satisfies $h_0$ followed by $f_0$ equal to $f_{X_0}$ (`hh₀`); $\lambda:\mathcal V.\iota\to\mathcal U.\iota$ is an index map with $\mathcal V.U\,w\le h_0^{-1}(\mathcal U.U(\lambda w))$ (`hlam₀`); $h_k:X_k\to A_k$ satisfies $h_k$ followed by $i_0$ equal to $j_0$ followed by $h_0$ (`hhk`) and lies over $\operatorname{Spec}k$ (`hhkf`), and is a homomorphism of the two group laws: for every base morphism $t$ and all pairs $P,Q$ of morphisms over $t$, the product $L_X.\mathrm{mul}\,t\,P\,Q$ followed by $h_k$ equals $L_k.\mathrm{mul}$ of the composites of $P$ and $Q$ with $h_k$ (`hhom`). Moreover $U^X_e\le h_k^{-1}(U_e)$ (`hUX`) and $(\mathcal V.\mathrm{comap}\,j_0).U\,w\le h_k^{-1}((\mathcal U.\mathrm{comap}\,i_0).U(\lambda w))$ for all $w$ (`hlamk`); and for each $w$ there is $h_Z\,w:Z\,w\to Y(\lambda w)$ over $\operatorname{Spec}T'$ (`hhZq`) compatible with the lifts, $g_Z\,w$ followed by $h_Z\,w$ being the composite of the open immersion of $\mathcal V.U\,w$, the restriction of $h_0$ and $g(\lambda w)$ (`hhZg`).
--
--   **Auxiliary comparison families.** $\Phi$ assigns to any two indices $a,b$ and any open $W\le\mathcal U.U\,a$, $W\le\mathcal U.U\,b$ an isomorphism $O\,a\,W\cong O\,b\,W$, subject to six laws: it lies over $\operatorname{Spec}T'$ (`hΦq`); it is pinned by the local lifts, any two lifts $\gamma,\gamma'$ of $W$ into the two charts satisfying $\gamma$ followed by $\Phi$ equal to $\gamma'$ (`hΦg`); it commutes with restriction to smaller opens (`hΦres`); it is the identity for $a=b$ (`hΦrefl`); the composite of $\Phi\,a\,b$ and $\Phi\,b\,a$ is the identity (`hΦsymm`); and it agrees with $\varphi\,a\,b$ on the pairwise overlap when $a<b$ (`hΦφ`). On the $X$-side, $\Phi_X$ assigns to $x<y$ and $W\le\mathcal V.U\,x\sqcap\mathcal V.U\,y$ an isomorphism $O_X\,x\,W\cong O_X\,y\,W$ compatible with $\varphi_X\,x\,y$ through the restriction morphisms (`hΦX`). Finally $\ell$ assigns to each $x$, each $W^X\subseteq X_0$ and $W^A\subseteq A_0$ with $W^X\le h_0^{-1}(W^A)$ a morphism $O_X\,x\,W^X\to O(\lambda x)\,W^A$ with $\ell$ followed by the inclusion of $O(\lambda x)\,W^A$ equal to the inclusion of $O_X\,x\,W^X$ followed by $h_Z\,x$ (`hℓ`).
--
--   **Conclusion.** With $\Gamma(A_k,U_e)$ regarded as a $k$-algebra via $f_k$, there exists a function
--   $$B:\Gamma(A_k,U_e)\to\operatorname{Dual}_k V\to (\mathrm{unit}\,f_{X_k}).\mathrm{cochain}\,(\mathcal V.\mathrm{comap}\,j_0)\,1,$$
--   with values in the degree-one Čech cochains of the structure sheaf of $X_k$ for the cover $\mathcal V.\mathrm{comap}\,j_0$, such that for every $t\in\mathcal V.\mathrm{Idx}\,1$, say $t=(x<y)$ with $x=t_0$, $y=t_1$, and with $C_t=\Gamma(Z\,x,O_X\,x(\mathcal V.\mathrm{inter}\,t))$ viewed as a $T'$-algebra via $q_Z\,x$, there exists
--   $$\beta:\Gamma(A_k,U_e)\to\operatorname{Hom}_k(V^\vee,\,k\otimes_{T'}C_t)$$
--   satisfying the following two conditions. First, $\beta$ is a system of tangent coordinates, in the sense of `IsTangentCoordsOfPairAtVia` for the ideal $\ker\pi$, the module $V$ and the map $\iota$, of the pair of morphisms $\operatorname{Spec}C_t\to Y(\lambda y)$ given by: the inverse of the `isoSpec` identification of $O_X\,x(\mathcal V.\mathrm{inter}\,t)$ with $\operatorname{Spec}C_t$, followed by $\Phi_X\,x\,y$ on $\mathcal V.\mathrm{inter}\,t$, then $\ell\,y$ from $\mathcal V.\mathrm{inter}\,t$ to $\mathcal U.U(\lambda x)\sqcap\mathcal U.U(\lambda y)$, then the inclusion of $O(\lambda y)(\mathcal U.U(\lambda x)\sqcap\mathcal U.U(\lambda y))$ into $Y(\lambda y)$; and, as second member, the same `isoSpec` inverse followed by $\ell\,x$ from $\mathcal V.\mathrm{inter}\,t$ to $\mathcal U.U(\lambda x)\sqcap\mathcal U.U(\lambda y)$, then $\Phi\,(\lambda x)\,(\lambda y)$ on $\mathcal U.U(\lambda x)\sqcap\mathcal U.U(\lambda y)$, then the same inclusion; the point datum being $f_k$, $L_k$, the open $i_0^{-1}(\mathcal U.U(\lambda y))$ of $A_k$ with the morphism given by the restriction of $i_0$ to it followed by $g(\lambda y)$, and the chart $U_e$. Second, $\sigma_X\,t(\beta\,a\,\xi)=B\,a\,\xi\,t$ for all $a\in\Gamma(A_k,U_e)$ and all $\xi\in V^\vee$. No linearity, derivation or cocycle property of $B$ itself is asserted.
--
--   This is the naturality step, one cohomological degree down and across the morphism $h_0$, in the analysis of obstructions to lifting a smooth scheme with relative group law along a small extension $\pi:T'\to T$: on each pairwise overlap of the $X$-side cover it compares the two ways of passing between charts, transition then lift, and lift then transition, and records the discrepancy as a $1$-cochain of tangent coordinates on $X_k$. It feeds [`AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom`](thm.html#AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom), where the coboundary of this $1$-cochain is shown to account for the difference of the two obstruction $2$-cocycles; its proof draws on the chartwise existence of tangent coordinates for a pair ([`AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia`](thm.html#AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia)), on the pinning of the comparison morphisms over $T'$ and modulo $\ker\pi$ ([`AlgebraicGeometry.SmallExtension.naturality_pair_comp_eq_and_quotient_comp_eq_of_local_lifts_hom`](thm.html#AlgebraicGeometry.SmallExtension.naturality_pair_comp_eq_and_quotient_comp_eq_of_local_lifts_hom)), and on flatness of sections of a flat morphism over affine opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_one_cochain_isTangentCoordsOfPairAtVia_pin_of_local_lifts_hom.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.exists_one_cochain_isTangentCoordsOfPairAtVia_pin_of_local_lifts_hom
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

    (σ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      ((ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))) ≃+* Γ(Ak, (𝒰.comap i₀).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))).toRingHom) ≫
          (hOaff (s.1 0) (𝒰.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 s) (𝒰.inter_le s 0)).fromSpec =
        Ak.homOfLE (𝒰.comap_inter_le i₀ s) ≫ (i₀ ∣_ 𝒰.inter s) ≫ A₀.homOfLE (𝒰.inter_le s 0) ≫ g (s.1 0))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒰.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      σ s (x ⊗ₜ[T'] (1 : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)))) = algebraMap (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter s) x)

    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
    (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (hρab : ∀ r : 𝒰.Idx 2,
      (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
          (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρbc : ∀ r : 𝒰.Idx 2,
      (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
        (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
          (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρac : ∀ r : 𝒰.Idx 2,
      (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
          (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ω : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2)))
    (hω : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      letI := algebraOfHom fk Ue
      ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs ∧
        ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r)
    (hωZ : letI := algebraOfHom fk Ue
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fk).d (𝒰.comap i₀) 2 (ω.1 a ξ) = 0)
    {X₀ : Scheme.{u}} (fX₀ : X₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated fX₀] [Smooth fX₀]

    (𝒱 : X₀.OrderedAffineCover)
    (Z : 𝒱.ι → Scheme.{u}) (qZ : ∀ a, Z a ⟶ Spec (CommRingCat.of T')) (hqZ : ∀ a, Smooth (qZ a))
    (gZ : ∀ a, (↑(𝒱.U a) : Scheme.{u}) ⟶ Z a)
    (hgZ : ∀ a, IsPullback (gZ a) ((𝒱.U a).ι ≫ fX₀) (qZ a) (Spec.map (CommRingCat.ofHom π)))

    {Xk : Scheme.{u}} (fXk : Xk ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fXk]
    (LX : RelativeGroupLaw (ResidueField T') fXk)
    (j₀ : Xk ⟶ X₀) [IsAffineHom j₀] (hj₀ : IsPullback j₀ fXk fX₀ (Spec.map (CommRingCat.ofHom ρ)))
    (UXe : Xk.Opens) (hUXe : IsAffineOpen UXe)
    (eX₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (UXe : Scheme.{u})) (heX₁ : eX₁ ≫ UXe.ι = (LX.one (𝟙 _)).1)

    (OX : ∀ a, X₀.Opens → (Z a).Opens)
    (hOX : ∀ (a : 𝒱.ι) (W : X₀.Opens), gZ a ⁻¹ᵁ OX a W = (𝒱.U a).ι ⁻¹ᵁ W)
    (hOXm : ∀ a, Monotone (OX a))
    (hOXtop : ∀ a, OX a (𝒱.U a) = ⊤)
    (hOXinf : ∀ (a : 𝒱.ι) (W W' : X₀.Opens), OX a W ⊓ OX a W' ≤ OX a (W ⊓ W'))
    (hOXaff : ∀ (a : 𝒱.ι) (W : X₀.Opens), IsAffineOpen W → W ≤ 𝒱.U a → IsAffineOpen (OX a W))

    (σX : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      ((ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))) ≃+* Γ(Xk, (𝒱.comap j₀).inter s))
    (hσX₁ : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σX s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))).toRingHom) ≫
          (hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).fromSpec =
        Xk.homOfLE (𝒱.comap_inter_le j₀ s) ≫ (j₀ ∣_ 𝒱.inter s) ≫ X₀.homOfLE (𝒱.inter_le s 0) ≫ gZ (s.1 0))
    (hσX₂ : ∀ {n : ℕ} (s : 𝒱.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom fXk ((𝒱.comap j₀).inter s)
      σX s (x ⊗ₜ[T'] (1 : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) = algebraMap (ResidueField T') Γ(Xk, (𝒱.comap j₀).inter s) x)

    (φX : ∀ (a b : 𝒱.ι), a < b → ((↑(OX a (𝒱.U a ⊓ 𝒱.U b)) : Scheme.{u}) ≅ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))))
    (hφXq : ∀ (a b : 𝒱.ι) (h : a < b),
      (φX a b h).hom ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ b = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ a)
    (hφXg : ∀ (a b : 𝒱.ι) (h : a < b),
      ∃ (γ : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX a (𝒱.U a ⊓ 𝒱.U b)))
        (γ' : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))),
        γ ≫ (OX a (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_left ≫ gZ a ∧
        γ' ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_right ≫ gZ b ∧
        γ ≫ (φX a b h).hom = γ')
    (hφXO : ∀ (a b : 𝒱.ι) (h : a < b) (W : X₀.Opens),
      (φX a b h).hom ⁻¹ᵁ ((OX b (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX b W) = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX a W)

    (ρXab : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 1) (𝒱.inter r))))
    (ρXbc : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 1) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (ρXac : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (hρXab : ∀ r : 𝒱.Idx 2,
      (ρXab r).hom ≫ (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) ≫
          (φX (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρXbc : ∀ r : 𝒱.Idx 2,
      (ρXbc r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) =
        (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) ≫
          (φX (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρXac : ∀ r : 𝒱.Idx 2,
      (ρXac r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) ≫
          (φX (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ωX : letI := algebraOfHom fXk UXe
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Xk, UXe)
          ((UXe.topIso.inv ≫ eX₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fXk).cochain (𝒱.comap j₀) 2)))
    (hωX : ∀ r : 𝒱.Idx 2,
      letI := algebraOfHom (qZ (r.1 0)) (OX (r.1 0) (𝒱.inter r))
      letI := algebraOfHom fXk UXe
      ∃ cs : Γ(Xk, UXe) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r))
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXac r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXab r).hom ≫ (ρXbc r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          fXk LX (j₀ ⁻¹ᵁ 𝒱.U (r.1 2)) ((j₀ ∣_ 𝒱.U (r.1 2)) ≫ gZ (r.1 2)) UXe cs ∧
        ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V), σX r (cs a ξ) = ωX.1 a ξ r)
    (hωXZ : letI := algebraOfHom fXk UXe
      ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fXk).d (𝒱.comap j₀) 2 (ωX.1 a ξ) = 0)

    (h₀ : X₀ ⟶ A₀) (hh₀ : h₀ ≫ f₀ = fX₀)
    (lam : 𝒱.ι → 𝒰.ι) (hlam₀ : ∀ w, 𝒱.U w ≤ h₀ ⁻¹ᵁ 𝒰.U (lam w))
    (hk : Xk ⟶ Ak) (hhk : hk ≫ i₀ = j₀ ≫ h₀) (hhkf : hk ≫ fk = fXk)
    (hhom : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fXk),
      (LX.mul t P Q).1 ≫ hk =
        (Lk.mul t ⟨P.1 ≫ hk, by rw [Category.assoc, hhkf, P.2]⟩ ⟨Q.1 ≫ hk, by rw [Category.assoc, hhkf, Q.2]⟩).1)
    (hUX : UXe ≤ hk ⁻¹ᵁ Ue)
    (hlamk : ∀ w, (𝒱.comap j₀).U w ≤ hk ⁻¹ᵁ (𝒰.comap i₀).U (lam w))
    (hZ : ∀ w, Z w ⟶ Y (lam w)) (hhZq : ∀ w, hZ w ≫ q (lam w) = qZ w)
    (hhZg : ∀ w, gZ w ≫ hZ w = X₀.homOfLE (hlam₀ w) ≫ (h₀ ∣_ 𝒰.U (lam w)) ≫ g (lam w))

    (Φ : ∀ (a b : 𝒰.ι) (W : A₀.Opens), W ≤ 𝒰.U a → W ≤ 𝒰.U b → ((↑(O a W) : Scheme.{u}) ≅ ↑(O b W)))
    (hΦq : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a)
    (hΦg : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b)
      (γ : (↑W : Scheme.{u}) ⟶ ↑(O a W)) (γ' : (↑W : Scheme.{u}) ⟶ ↑(O b W)),
      γ ≫ (O a W).ι = A₀.homOfLE ha ≫ g a → γ' ≫ (O b W).ι = A₀.homOfLE hb ≫ g b → γ ≫ (Φ a b W ha hb).hom = γ')
    (hΦres : ∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
      (hWW : W' ≤ W),
      (Φ a b W' ha' hb').hom ≫ (Y b).homOfLE (hOm b hWW) = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom)
    (hΦrefl : ∀ (a : 𝒰.ι) (W : A₀.Opens) (ha ha' : W ≤ 𝒰.U a), (Φ a a W ha ha').hom = 𝟙 _)
    (hΦsymm : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (Φ b a W hb ha).hom = 𝟙 _)
    (hΦφ : ∀ (a b : 𝒰.ι) (h : a < b), (Φ a b (𝒰.U a ⊓ 𝒰.U b) inf_le_left inf_le_right).hom = (φ a b h).hom)

    (ΦX : ∀ (x y : 𝒱.ι), x < y → ∀ (W : X₀.Opens), W ≤ 𝒱.U x ⊓ 𝒱.U y → ((↑(OX x W) : Scheme.{u}) ≅ ↑(OX y W)))
    (hΦX : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW : W ≤ 𝒱.U x ⊓ 𝒱.U y),
      (ΦX x y h W hW).hom ≫ (Z y).homOfLE (hOXm y hW) = (Z x).homOfLE (hOXm x hW) ≫ (φX x y h).hom)

    (ℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens), WX ≤ h₀ ⁻¹ᵁ WA → ((↑(OX x WX) : Scheme.{u}) ⟶ ↑(O (lam x) WA)))
    (hℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens) (h : WX ≤ h₀ ⁻¹ᵁ WA),
      ℓ x WX WA h ≫ (O (lam x) WA).ι = (OX x WX).ι ≫ hZ x)
    :
    letI := algebraOfHom fk Ue
    ∃ B : Γ(Ak, Ue) → Module.Dual (ResidueField T') V → (OModulePresheaf.unit fXk).cochain (𝒱.comap j₀) 1,
      ∀ t : 𝒱.Idx 1,
        letI := algebraOfHom (qZ (t.1 0)) (OX (t.1 0) (𝒱.inter t))
        ∃ β : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Z (t.1 0), OX (t.1 0) (𝒱.inter t)))),
          IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (t.1 0), OX (t.1 0) (𝒱.inter t))
            ((hOXaff (t.1 0) (𝒱.inter t) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 t) (𝒱.inter_le t 0)).isoSpec.inv ≫
                (ΦX (t.1 0) (t.1 1) (t.2 (by decide)) (𝒱.inter t) (le_inf (𝒱.inter_le t 0) (𝒱.inter_le t 1))).hom ≫
                ℓ (t.1 1) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (by rw [Scheme.Hom.preimage_inf]; exact le_inf ((𝒱.inter_le t 0).trans (hlam₀ (t.1 0))) ((𝒱.inter_le t 1).trans (hlam₀ (t.1 1)))) ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι)
            ((hOXaff (t.1 0) (𝒱.inter t) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 t) (𝒱.inter_le t 0)).isoSpec.inv ≫
                ℓ (t.1 0) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (by rw [Scheme.Hom.preimage_inf]; exact le_inf ((𝒱.inter_le t 0).trans (hlam₀ (t.1 0))) ((𝒱.inter_le t 1).trans (hlam₀ (t.1 1)))) ≫
                (Φ (lam (t.1 0)) (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) inf_le_left inf_le_right).hom ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι)
            fk Lk (i₀ ⁻¹ᵁ 𝒰.U (lam (t.1 1))) ((i₀ ∣_ 𝒰.U (lam (t.1 1))) ≫ g (lam (t.1 1))) Ue β ∧
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σX t (β a ξ) = B a ξ t := by sorry
