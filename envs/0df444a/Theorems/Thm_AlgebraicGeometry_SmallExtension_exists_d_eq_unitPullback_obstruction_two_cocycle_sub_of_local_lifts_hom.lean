-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom
-- name    : AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/8422e3e4-2582-5acd-9ae0-bf5fdd594216
-- title:
--   Naturality of the obstruction 2-cocycle along a homomorphic lift
-- statement:
--   Throughout, $T'$ is an Artinian local commutative ring with residue field $k=\mathrm{ResidueField}\,T'$, $T$ a commutative ring, and $\pi\colon T'\to T$ a surjective ring homomorphism.
--
--   **Coefficient data.** The hypotheses on $\pi$ are: `hπ` surjectivity, `hker` nilpotence of $\ker\pi$, `hsmall` the smallness condition $\ker\pi\cdot\mathfrak m_{T'}=0$, and `hI` the inclusion $\ker\pi\subseteq\mathfrak m_{T'}$. A ring homomorphism $\rho\colon T\to k$ is given with `hρ` : $\rho\circ\pi$ equal to the residue map of $T'$. Further, $V$ is a $k$-vector space of finite dimension, equipped also with a $T'$-module structure compatible with the $k$-structure and with a central right $k$-action, and $\iota\colon V\to T'$ is a $T'$-linear map which is injective (`hι`) and whose range is exactly $\ker\pi$ viewed as a $T'$-submodule of $T'$ (`hιI`); so $V\cong\ker\pi$.
--
--   **$A$-side lifting frame.** $f_0\colon A_0\to\operatorname{Spec} T$ is separated and smooth, and $\mathcal U$ is an ordered affine cover of $A_0$: a finite linearly ordered index set $\mathcal U.\iota$ together with affine opens $U_a$ whose supremum is $\top$. For each $a$ there are a scheme $Y_a$, a smooth morphism $q_a\colon Y_a\to\operatorname{Spec} T'$ (`hq`) and $g_a\colon U_a\to Y_a$ such that the square with $g_a$, $U_a\hookrightarrow A_0\to\operatorname{Spec}T$, $q_a$ and $\operatorname{Spec}\pi$ is a pullback (`hg`); thus $Y_a$ is a smooth lift of $U_a$ over $T'$. On the special fibre, $f_k\colon A_k\to\operatorname{Spec}k$ is separated, $L_k$ is a relative group law for $f_k$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec}k$, with associativity, unit, inverse and base-change naturality axioms), $i_0\colon A_k\to A_0$ is an affine morphism exhibiting $f_k$ as the base change of $f_0$ along $\operatorname{Spec}\rho$ (`hi₀`), $U_e\subseteq A_k$ is an affine open (`hUe`) and $e_1\colon\operatorname{Spec}k\to U_e$ is a lift of the unit section of $L_k$ (`he₁`).
--
--   The opens of the lifts are organised by $O_a\colon A_0.\mathrm{Opens}\to(Y_a).\mathrm{Opens}$ subject to five conditions: `hO` ($g_a^{-1}O_a(W)$ equals the preimage of $W$ in $U_a$), `hOm` (monotonicity), `hOtop` ($O_a(U_a)=\top$), `hOinf` ($O_a(W)\sqcap O_a(W')\le O_a(W\sqcap W')$) and `hOaff` (affineness of $O_a(W)$ for $W$ affine with $W\le U_a$). For every $n$ and every strictly increasing $(n+1)$-tuple $s$ in $\mathcal U.\iota$, with $\mathcal U.\mathrm{inter}\,s=\bigsqcap_j U_{s_j}$, a ring isomorphism $\sigma_s\colon k\otimes_{T'}\Gamma(Y_{s_0},O_{s_0}(\mathcal U.\mathrm{inter}\,s))\cong\Gamma(A_k,(i_0^{-1}\mathcal U).\mathrm{inter}\,s)$ is given, together with `hσ₁`, the identification of $\operatorname{Spec}\sigma_s$ followed by $\operatorname{Spec}$ of the right inclusion of the tensor product and the canonical map from $\operatorname{Spec}$ of the sections with the restriction of $i_0$ followed by $g_{s_0}$, and `hσ₂`, the statement that $\sigma_s(x\otimes 1)$ is the structure map image of $x\in k$.
--
--   Transition data: for $a<b$, isomorphisms $\varphi_{ab}\colon O_a(U_a\sqcap U_b)\cong O_b(U_a\sqcap U_b)$ with `hφq` (compatibility with $q_a,q_b$ over $T'$), `hφg` (existence of sections $\gamma,\gamma'$ of the two lifts over $U_a\sqcap U_b$ with $\gamma$ followed by $\varphi_{ab}$ equal to $\gamma'$) and `hφO` (compatibility of $\varphi_{ab}$ with the systems $O_a$, $O_b$ on preimages). For each strictly increasing triple $r$, isomorphisms $\rho^{ab}_r,\rho^{bc}_r,\rho^{ac}_r$ between the corresponding opens $O_{r_i}(\mathcal U.\mathrm{inter}\,r)$ are given, each restricting the relevant $\varphi$ along the inclusions of opens (`hρab`, `hρbc`, `hρac`).
--
--   The obstruction datum is $\omega$, an element of $\mathrm{PointDerivations}_k(\Gamma(A_k,U_e),\mathrm{ev})$ with values in $\operatorname{Hom}_k(V^\vee,\;C^2)$, where $\mathrm{ev}$ is evaluation at the unit point $e_1$ and $C^2$ denotes the degree-$2$ Čech cochains of the module presheaf $U\mapsto\Gamma(A_k,U)$ (`OModulePresheaf.unit` $f_k$) for the cover $i_0^{-1}\mathcal U$; being a point derivation means $\omega(ab)=\mathrm{ev}(a)\,\omega(b)+\mathrm{ev}(b)\,\omega(a)$. Its meaning is pinned by `hω`: for each triple $r$ there is a family $cs$ of $V^\vee$-indexed coordinates with values in $k\otimes_{T'}\Gamma(Y_{r_0},O_{r_0}(\mathcal U.\mathrm{inter}\,r))$ satisfying `IsTangentCoordsOfPairAtVia` for the ideal $\ker\pi$, the module $V$ with $\iota$, the two morphisms from $\operatorname{Spec}$ of those sections into $O_{r_2}(\mathcal U.\mathrm{inter}\,r)\subseteq Y_{r_2}$ obtained from $\rho^{ac}_r$ and from $\rho^{ab}_r$ followed by $\rho^{bc}_r$, the group law $L_k$, the open $i_0^{-1}U_{r_2}$ with the map to $Y_{r_2}$ induced by $i_0$ and $g_{r_2}$, and the chart $U_e$; unfolded, this asserts the existence of a point $w_0$ of that open over the thickening ring, lying over the prescribed base map, which is a tangent vector of the pair of the two morphisms in the sense of `IsTangentOfPair` (a Schlessinger map from the pair ring factoring the two morphisms), and of $w_1\colon\operatorname{Spec}(\text{thickening})\to U_e$ equal to the $L_k$-translate of $w_0$ to the unit, such that $cs$ is the coordinate function of the chart ring homomorphism of $w_1$; moreover $\sigma_r(cs(a)(\xi))=\omega(a)(\xi)(r)$ for all $a$ and $\xi$. Finally `hωZ` says that each cochain $\omega(a)(\xi)$ is a cocycle: its Čech differential in degree $2$ vanishes.
--
--   **$X$-side lifting frame.** The same package is given for a separated smooth $f_{X_0}\colon X_0\to\operatorname{Spec}T$: an ordered affine cover $\mathcal V$, smooth lifts $Z_w$, $q^Z_w$ (`hqZ`), $g^Z_w$ with pullback squares (`hgZ`); a separated special fibre $f_{X_k}\colon X_k\to\operatorname{Spec}k$ with relative group law $L_X$, the affine morphism $j_0$ exhibiting the base change (`hj₀`), an affine open $U^X_e$ (`hUXe`) with unit lift $e^X_1$ (`heX₁`); opens $O^X$ with the five conditions `hOX`, `hOXm`, `hOXtop`, `hOXinf`, `hOXaff`; chart identifications $\sigma^X$ with `hσX₁`, `hσX₂`; transitions $\varphi^X$ with `hφXq`, `hφXg`, `hφXO`; triple comparisons $\rho^{X,ab},\rho^{X,bc},\rho^{X,ac}$ with `hρXab`, `hρXbc`, `hρXac`; and a point derivation $\omega^X$ on $\Gamma(X_k,U^X_e)$ with values in $\operatorname{Hom}_k(V^\vee,C^2)$ for the cover $j_0^{-1}\mathcal V$, pinned by `hωX` exactly as above and satisfying the cocycle condition `hωXZ`.
--
--   **Morphism data.** A morphism $h_0\colon X_0\to A_0$ over $\operatorname{Spec}T$ (`hh₀` : $h_0$ followed by $f_0$ is $f_{X_0}$); an index map $\mathrm{lam}\colon\mathcal V.\iota\to\mathcal U.\iota$ with $\mathcal V.U_w\le h_0^{-1}\mathcal U.U_{\mathrm{lam}\,w}$ (`hlam₀`); a morphism $h_k\colon X_k\to A_k$ with `hhk` ($h_k$ followed by $i_0$ equals $j_0$ followed by $h_0$) and `hhkf` ($h_k$ followed by $f_k$ is $f_{X_k}$); the homomorphism property `hhom`: for every scheme $S$ with $t\colon S\to\operatorname{Spec}k$ and all $P,Q$ in $\mathrm{SchemeHomOver}\,t\,f_{X_k}$, the underlying morphism of $L_X.\mathrm{mul}\,t\,P\,Q$ followed by $h_k$ equals that of $L_k.\mathrm{mul}\,t$ applied to $P$ and $Q$ composed with $h_k$; the chart compatibility `hUX` : $U^X_e\le h_k^{-1}U_e$; the cover compatibility `hlamk` : $(j_0^{-1}\mathcal V).U_w\le h_k^{-1}\big((i_0^{-1}\mathcal U).U_{\mathrm{lam}\,w}\big)$; and lifts of $h_0$ on the charts, namely $\tilde h_w\colon Z_w\to Y_{\mathrm{lam}\,w}$ with `hhZq` ($\tilde h_w$ followed by $q_{\mathrm{lam}\,w}$ equals $q^Z_w$) and `hhZg` ($g^Z_w$ followed by $\tilde h_w$ equals the inclusion-induced map $\mathcal V.U_w\to h_0^{-1}\mathcal U.U_{\mathrm{lam}\,w}$ followed by the restriction of $h_0$ and by $g_{\mathrm{lam}\,w}$).
--
--   **Conclusion.** For every section $a\in\Gamma(A_k,U_e)$ and every $\xi\in V^\vee=\operatorname{Hom}_k(V,k)$ there exists a degree-$1$ Čech cochain $b$ of the unit module presheaf of $f_{X_k}$ for the cover $j_0^{-1}\mathcal V$ such that
--   $$\mathrm{unitPullback}\,h_k\,(j_0^{-1}\mathcal V)\,(i_0^{-1}\mathcal U)\,\mathrm{lam}\,\mathrm{hlamk}\;2\;\big(\omega(a)(\xi)\big)\;-\;\omega^X\big(a|^{h_k}\big)(\xi)\;=\;d^1 b,$$
--   where $a|^{h_k}$ denotes the image of $a$ under $h_k^\sharp$ on $U_e$ restricted along $U^X_e\le h_k^{-1}U_e$, $d^1$ is the Čech differential from degree $1$ to degree $2$, and the pullback operator $\mathrm{unitPullback}$ sends a $2$-cochain $z$ on $i_0^{-1}\mathcal U$ to the $2$-cochain whose value at a strictly increasing triple $s$ is $0$ if $\mathrm{lam}\circ s$ fails to be injective, and otherwise the sign of the sorting permutation of $\mathrm{lam}\circ s$ times the restriction of $h_k^\sharp\big(z(\text{sorted }\mathrm{lam}\circ s)\big)$ to the intersection indexed by $s$. Thus the two obstruction $2$-cocycles agree after pullback along $h_k$ up to a coboundary.
--
--   This is the functoriality (naturality) statement for the obstruction cocycle to lifting a smooth separated $T$-scheme with a group law along a small extension $T'\to T$: along a $T$-morphism $h_0$ admitting lifts on the charts and whose special fibre $h_k$ is a homomorphism for the two group laws, the pullback of the obstruction $2$-cocycle of the target agrees with the obstruction $2$-cocycle of the source modulo coboundaries, i.e. the obstruction classes in $H^2$ correspond under $h_k^*$. It is the cochain-level input to [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_obstruction_two_cocycle`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_obstruction_two_cocycle), where it is applied to the multiplication and the two projections in order to compare the obstruction of a product with those of its factors; the proof combines the pinning lemma for one-cochains with the corresponding identity for pinned cochains, together with the transition-isomorphism machinery for ordered affine covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom.lean

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

theorem AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom
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
    (hhZg : ∀ w, gZ w ≫ hZ w = X₀.homOfLE (hlam₀ w) ≫ (h₀ ∣_ 𝒰.U (lam w)) ≫ g (lam w)) :
    letI := algebraOfHom fk Ue
    letI := algebraOfHom fXk UXe
    ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
      ∃ b : (OModulePresheaf.unit fXk).cochain (𝒱.comap j₀) 1,
        OModulePresheaf.unitPullback (πX := fXk) hk (𝒱.comap j₀) (𝒰.comap i₀) lam hlamk 2 (ω.1 a ξ) -
            ωX.1 ((Xk.presheaf.map (homOfLE hUX).op).hom ((hk.app Ue).hom a)) ξ =
          (OModulePresheaf.unit fXk).d (𝒱.comap j₀) 1 b := by sorry
