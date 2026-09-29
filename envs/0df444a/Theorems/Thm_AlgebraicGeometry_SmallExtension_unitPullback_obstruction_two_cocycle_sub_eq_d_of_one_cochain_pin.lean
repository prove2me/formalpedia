-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin
-- name    : AlgebraicGeometry.SmallExtension.unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/db449420-4bb4-5c58-ae07-a13c85407039
-- title:
--   Pulled-back obstruction cocycle minus obstruction cocycle is a coboundary
-- statement:
--   **The small extension.** $T'$ is a local artinian ring and $\pi \colon T' \to T$ a ring homomorphism which is surjective (`hπ`), has nilpotent kernel (`hker`), satisfies $\ker\pi \cdot \mathfrak m_{T'} = 0$ (`hsmall`) and $\ker\pi \subseteq \mathfrak m_{T'}$ (`hI`). A homomorphism $\rho \colon T \to k$, $k :=$ `ResidueField T'`, is given with $\rho \circ \pi$ the residue map of $T'$ (`hρ`). Further, $V$ is a finite-dimensional $k$-vector space carrying in addition a $T'$-module structure compatible with the $k$-structure (and the standard central-scalar data for the opposite action of $k$), and $\iota \colon V \to T'$ is an injective $T'$-linear map (`hι`) whose image is exactly $\ker\pi$, viewed as a $T'$-submodule (`hιI`).
--
--   **The $A$-side.** $f_0 \colon A_0 \to \operatorname{Spec} T$ is separated and smooth, and $\mathcal U$ is an ordered affine cover of $A_0$: a finite linearly ordered index set $\mathcal U.\iota$ together with affine opens $U_a$ whose supremum is $\top$. For each $a$ a scheme $Y_a$ is given with a morphism $q_a \colon Y_a \to \operatorname{Spec} T'$ which is smooth (`hq`), and $g_a \colon U_a \to Y_a$ such that the square formed by $g_a$, the composite $U_a \hookrightarrow A_0 \to \operatorname{Spec} T$, $q_a$ and $\operatorname{Spec}\pi$ is a pullback (`hg`); thus $Y_a$ is a smooth lift of $U_a$ across $\pi$.
--
--   On the residue-field fibre: $f_k \colon A_k \to \operatorname{Spec} k$ is separated, $L_k$ is a relative group law for $f_k$ (functorial multiplication, unit and inverse on $S$-points over $\operatorname{Spec} k$, with associativity, both unit laws, left inverse and naturality under base change), $i_0 \colon A_k \to A_0$ is an affine morphism exhibiting $A_k$ as the base change of $A_0$ along $\operatorname{Spec}\rho$ (`hi₀`), $U_e \subseteq A_k$ is an affine open (`hUe`) and $e_1 \colon \operatorname{Spec} k \to U_e$ is a morphism whose composite with the inclusion is the unit section $L_k.\mathrm{one}(\mathrm{id})$ (`he₁`).
--
--   The opens of the lifts are organised by a family $O_a \colon A_0.\mathrm{Opens} \to (Y_a).\mathrm{Opens}$ subject to five laws: $g_a^{-1}(O_a W)$ is the preimage of $W$ in $U_a$ (`hO`), $O_a$ is monotone (`hOm`), $O_a(U_a) = \top$ (`hOtop`), $O_a W \cap O_a W' \le O_a(W \cap W')$ (`hOinf`), and $O_a W$ is affine whenever $W$ is affine and $W \le U_a$ (`hOaff`).
--
--   For every $n$ and every strictly increasing tuple $s \colon \{0,\dots,n\} \to \mathcal U.\iota$, writing $\mathcal U.\mathrm{inter}\,s = \bigcap_j U_{s(j)}$, a ring isomorphism
--   $\sigma_s \colon k \otimes_{T'} \Gamma(Y_{s(0)}, O_{s(0)}(\mathcal U.\mathrm{inter}\,s)) \to \Gamma(A_k, (\mathcal U.\mathrm{comap}\,i_0).\mathrm{inter}\,s)$ is given (the comap cover of $A_k$ has opens $i_0^{-1}U_a$), subject to the geometric compatibility `hσ₁` (the canonical isomorphism onto $\operatorname{Spec}$ of the left-hand side, followed by $\operatorname{Spec}\sigma_s$ read backwards, the right inclusion into the tensor product and `fromSpec`, equals the canonical map $(\mathcal U.\mathrm{comap}\,i_0).\mathrm{inter}\,s \to A_k \to A_0 \to Y_{s(0)}$ built from $i_0$ and $g_{s(0)}$) and to $k$-linearity on the left tensor factor (`hσ₂`: $\sigma_s(x \otimes 1)$ is the structural image of $x$).
--
--   Transition isomorphisms $\varphi_{ab} \colon O_a(U_a \cap U_b) \cong O_b(U_a \cap U_b)$ for $a < b$ are given, commuting with the structure maps to $\operatorname{Spec} T'$ (`hφq`), compatible with the lifts (`hφg`: there are $\gamma, \gamma'$ factoring the restrictions of $g_a$, $g_b$ through $O_a$, $O_b$ with $\gamma$ followed by $\varphi_{ab}$ equal to $\gamma'$), and compatible with the $O$-opens (`hφO`). For each triple $r \in \mathcal U.\mathrm{Idx}\,2$, three isomorphisms $\rho^{ab}_r, \rho^{bc}_r, \rho^{ac}_r$ between the $O_{r(i)}(\mathcal U.\mathrm{inter}\,r)$ for $i = 0,1$; $1,2$; $0,2$ are given, each compatible with the corresponding $\varphi$ after the inclusions of the triple intersection into the pairwise intersections (`hρab`, `hρbc`, `hρac`).
--
--   The obstruction datum is $\omega$, an element of [`Algebra.PointDerivations`](def/Algebra_PointDerivations.html#L9) $k$ $\Gamma(A_k,U_e)$ at the evaluation homomorphism induced by $e_1$, with values in $\operatorname{Hom}_k(V^\vee, C^2)$, where $C^2 =$ `(OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2` is the group of $2$-cochains $s \mapsto \Gamma(A_k, \mathrm{inter}\,s)$ for the comap cover: so $\omega.1$ is $k$-linear and satisfies the Leibniz rule $\omega.1(ab) = \mathrm{ev}(a)\,\omega.1(b) + \mathrm{ev}(b)\,\omega.1(a)$ at that evaluation. It is pinned by `hω`: for every triple $r$ there is a family $cs$ on $\Gamma(A_k,U_e)$ with values in $\operatorname{Hom}_k(V^\vee, k \otimes_{T'} \Gamma(Y_{r(0)}, O_{r(0)}(\mathcal U.\mathrm{inter}\,r)))$ which is `IsTangentCoordsOfPairAtVia` for $\ker\pi$, $V$, $\iota$, the ring $C_r = \Gamma(Y_{r(0)}, O_{r(0)}(\mathcal U.\mathrm{inter}\,r))$ and the two morphisms $\operatorname{Spec} C_r \to Y_{r(2)}$ obtained from the canonical identification of $\operatorname{Spec} C_r$ with $O_{r(0)}(\mathcal U.\mathrm{inter}\,r)$ followed by $\rho^{ac}_r$, respectively by $\rho^{ab}_r$ then $\rho^{bc}_r$, and then the inclusion of $O_{r(2)}(\mathcal U.\mathrm{inter}\,r)$ into $Y_{r(2)}$, taken relative to $f_k$, $L_k$, the open $i_0^{-1}U_{r(2)}$ with the map $(i_0 \mid_{U_{r(2)}})$ followed by $g_{r(2)}$, and the chart open $U_e$; and $\sigma_r(cs\,a\,\xi) = \omega.1\,a\,\xi\,r$ for all $a$, $\xi$. Here `IsTangentCoordsOfPairAtVia` asserts the existence of a point $w_0$ of the given open over the thickening $(k \otimes_{T'} C_r) \otimes_k (k \oplus V)$, lying over the canonical base map, such that $w_0$ followed by the given map presents the pair of morphisms as a tangent pair for $\ker\pi$ through a Schlessinger map out of the pair ring, together with a morphism $w_1$ into $U_e$ whose composite with the inclusion is the translate of $w_0$ by the group law $L_k$ to the unit section, and such that the family equals the tangent coordinates of the chart homomorphism $\Gamma(A_k,U_e) \to$ thickening determined by $w_1$. Finally `hωZ` states that $\omega.1\,a\,\xi$ is a cocycle: its image under the degree-$2$ coboundary operator `d` of `OModulePresheaf.unit fk` for the cover $\mathcal U.\mathrm{comap}\,i_0$ vanishes, for all $a$ and $\xi$.
--
--   **The $X$-side.** The same data are given over $X_0$: a separated smooth $f_{X_0} \colon X_0 \to \operatorname{Spec} T$, an ordered affine cover $\mathcal V$, smooth lifts $Z_w \to \operatorname{Spec} T'$ via $q^Z_w$ (`hqZ`) with pullback squares `hgZ` for $g^Z_w$, a separated $f_{X_k} \colon X_k \to \operatorname{Spec} k$ with relative group law $L_X$, an affine morphism $j_0$ exhibiting $X_k$ as the base change along $\operatorname{Spec}\rho$ (`hj₀`), an affine open $U^X_e$ (`hUXe`) with a morphism $e^X_1$ onto the unit section (`heX₁`), a family $O^X$ with the same five laws (`hOX`, `hOXm`, `hOXtop`, `hOXinf`, `hOXaff`), isomorphisms $\sigma^X_s$ with the two compatibilities (`hσX₁`, `hσX₂`), transitions $\varphi^X_{xy}$ with the three laws (`hφXq`, `hφXg`, `hφXO`), triple isomorphisms $\rho^{X,ab}, \rho^{X,bc}, \rho^{X,ac}$ with their three compatibilities (`hρXab`, `hρXbc`, `hρXac`), and a point derivation $\omega^X$ with values in $\operatorname{Hom}_k(V^\vee, \text{$2$-cochains on } \mathcal V.\mathrm{comap}\,j_0)$, pinned on every triple in the same way (`hωX`) and a cocycle (`hωXZ`).
--
--   **The morphism.** A morphism $h_0 \colon X_0 \to A_0$ over $\operatorname{Spec} T$ is given (`hh₀`), a map of index sets $\lambda$ with $\mathcal V.U_w \le h_0^{-1}\mathcal U.U_{\lambda w}$ (`hlam₀`), and $h_k \colon X_k \to A_k$ with $h_k$ followed by $i_0$ equal to $j_0$ followed by $h_0$ (`hhk`) and $h_k$ followed by $f_k$ equal to $f_{X_k}$ (`hhkf`). The hypothesis `hhom` says $h_k$ is a homomorphism of group laws: for every $S$, every $t \colon S \to \operatorname{Spec} k$ and all $S$-points $P$, $Q$ of $X_k$ over $t$, the product $L_X.\mathrm{mul}\,t\,P\,Q$ followed by $h_k$ equals $L_k.\mathrm{mul}\,t$ of $P$ followed by $h_k$ and $Q$ followed by $h_k$. Moreover $U^X_e \le h_k^{-1}U_e$ (`hUX`), $(\mathcal V.\mathrm{comap}\,j_0).U_w \le h_k^{-1}(\mathcal U.\mathrm{comap}\,i_0).U_{\lambda w}$ (`hlamk`), and morphisms $h^Z_w \colon Z_w \to Y_{\lambda w}$ over $\operatorname{Spec} T'$ (`hhZq`) compatible with the lifts and $h_0$ (`hhZg`).
--
--   **Auxiliary transition and comparison families.** On the $A$-side, $\Phi_{a,b,W}$ is an isomorphism $O_a W \cong O_b W$ for every pair $a,b$ and every open $W$ with $W \le U_a$ and $W \le U_b$, subject to six laws: compatibility with the structure maps to $\operatorname{Spec} T'$ (`hΦq`); rigidity with respect to the lifts (`hΦg`: any $\gamma,\gamma'$ factoring the restrictions of $g_a,g_b$ satisfy $\gamma$ followed by $\Phi_{a,b,W}$ equal to $\gamma'$); compatibility with restriction to a smaller $W'$ (`hΦres`); $\Phi_{a,a,W} = \mathrm{id}$ (`hΦrefl`); $\Phi_{a,b,W}$ followed by $\Phi_{b,a,W}$ is the identity (`hΦsymm`); and $\Phi_{a,b,U_a \cap U_b} = \varphi_{ab}$ for $a<b$ (`hΦφ`). On the $X$-side, $\Phi^X_{x,y,W}$ is given for $x<y$ and $W \le \mathcal V.U_x \cap \mathcal V.U_y$, compatible with $\varphi^X_{xy}$ after the inclusions (`hΦX`). Finally $\ell_x(W^X, W^A) \colon O^X_x W^X \to O_{\lambda x} W^A$ is given whenever $W^X \le h_0^{-1}W^A$, with $\ell_x$ followed by the inclusion into $Y_{\lambda x}$ equal to the inclusion of $O^X_x W^X$ followed by $h^Z_x$ (`hℓ`).
--
--   **The pinned $1$-cochain.** $B$ assigns to $a \in \Gamma(A_k,U_e)$ and $\xi \in V^\vee$ a $1$-cochain for `OModulePresheaf.unit fXk` on the cover $\mathcal V.\mathrm{comap}\,j_0$, pinned by `hB`: for every pair $t \in \mathcal V.\mathrm{Idx}\,1$ (that is, $t(0) < t(1)$) there is a family $\beta$ on $\Gamma(A_k,U_e)$ with values in $\operatorname{Hom}_k(V^\vee, k \otimes_{T'} \Gamma(Z_{t(0)}, O^X_{t(0)}(\mathcal V.\mathrm{inter}\,t)))$ which is `IsTangentCoordsOfPairAtVia` for $\ker\pi$, $V$, $\iota$, the ring $\Gamma(Z_{t(0)}, O^X_{t(0)}(\mathcal V.\mathrm{inter}\,t))$ and the two morphisms from its spectrum to $Y_{\lambda t(1)}$ obtained, after the canonical identification of the spectrum with $O^X_{t(0)}(\mathcal V.\mathrm{inter}\,t)$, as $\Phi^X_{t(0),t(1),\mathcal V.\mathrm{inter}\,t}$ then $\ell_{t(1)}$ then the inclusion of $O_{\lambda t(1)}(U_{\lambda t(0)} \cap U_{\lambda t(1)})$, respectively as $\ell_{t(0)}$ then $\Phi_{\lambda t(0),\lambda t(1),U_{\lambda t(0)} \cap U_{\lambda t(1)}}$ then that same inclusion, taken relative to $f_k$, $L_k$, the open $i_0^{-1}U_{\lambda t(1)}$ with the map $(i_0 \mid_{U_{\lambda t(1)}})$ followed by $g_{\lambda t(1)}$, and the chart open $U_e$; and $\sigma^X_t(\beta\,a\,\xi) = B\,a\,\xi\,t$ for all $a$ and $\xi$.
--
--   **Conclusion.** For every $a \in \Gamma(A_k,U_e)$, every $\xi \in V^\vee$ and every triple $s \in \mathcal V.\mathrm{Idx}\,2$,
--   $$\bigl(\mathrm{unitPullback}\ h_k,\ \lambda,\ \text{degree } 2\bigr)(\omega.1\,a\,\xi)(s) \; - \; \omega^X.1\bigl(\text{$h_k^\sharp a$ restricted to } U^X_e\bigr)(\xi)(s) \;=\; \bigl(d^1 (B\,a\,\xi)\bigr)(s),$$
--   an identity in $\Gamma(X_k, (\mathcal V.\mathrm{comap}\,j_0).\mathrm{inter}\,s)$. Here `OModulePresheaf.unitPullback hk (𝒱.comap j₀) (𝒰.comap i₀) lam hlamk 2` sends a $2$-cochain $z$ on the $A_k$-side cover to the cochain whose value at $s$ is, when $\lambda \circ s$ is injective, the sign of the permutation sorting $\lambda \circ s$ times the restriction along $\mathcal V.\mathrm{inter}\,s \le h_k^{-1}$ of the sorted intersection of the image of $z$ at the sorted triple under $h_k$ on sections, and $0$ otherwise; $h_k^\sharp a$ denotes the image of $a$ under $h_k$ on sections over $U_e$, restricted to $U^X_e$ along `hUX`; and $d^1$ is the coboundary operator `d` of `OModulePresheaf.unit fXk` in degree $1$ for the cover $\mathcal V.\mathrm{comap}\,j_0$.
--
--   This is the cochain-level naturality step in the comparison of the two obstruction classes attached, by the Čech computation for a small extension $T' \to T$, to a morphism $h_0$ between two smooth separated $T$-schemes with relative group laws on their residue-field fibres: the pulled-back obstruction $2$-cocycle of the target and the obstruction $2$-cocycle of the source differ on every triple overlap by the coboundary of the pinned pair-cochain $B$. It is used by [`AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom`](thm.html#AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom), which removes the auxiliary transition, restriction and pinning families and asserts only the existence of such a $1$-cochain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin.lean

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

theorem AlgebraicGeometry.SmallExtension.unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin
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

    (B : Γ(Ak, Ue) → Module.Dual (ResidueField T') V → (OModulePresheaf.unit fXk).cochain (𝒱.comap j₀) 1)
    (hB :
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
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σX t (β a ξ) = B a ξ t)
    :
    letI := algebraOfHom fk Ue
    letI := algebraOfHom fXk UXe
    ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V) (s : 𝒱.Idx 2),
      OModulePresheaf.unitPullback (πX := fXk) hk (𝒱.comap j₀) (𝒰.comap i₀) lam hlamk 2 (ω.1 a ξ) s -
          ωX.1 ((Xk.presheaf.map (homOfLE hUX).op).hom ((hk.app Ue).hom a)) ξ s =
        (OModulePresheaf.unit fXk).d (𝒱.comap j₀) 1 (B a ξ) s := by sorry
