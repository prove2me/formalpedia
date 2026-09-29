-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary
-- name    : AlgebraicGeometry.SmallExtension.exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/96002384-645f-585c-aadc-048e5e70837a
-- title:
--   Coboundary modification of overlap isomorphisms into a cocycle
-- statement:
--   Throughout, $T'$ is a commutative local Artinian ring and $T$ a commutative ring, $\pi \colon T' \to T$ a surjective ring homomorphism whose kernel is nilpotent and satisfies $(\ker \pi)\cdot \mathfrak m_{T'} = 0$ and $\ker\pi \subseteq \mathfrak m_{T'}$, and $f_0 \colon A_0 \to \operatorname{Spec} T$ is a separated smooth morphism. A ring homomorphism $\rho \colon T \to \kappa$, where $\kappa =$ `ResidueField T'`, is given with $\rho \circ \pi$ equal to the residue map of $T'$. The module $V$ is a finite-dimensional $\kappa$-vector space, also a $T'$-module compatibly (scalar tower, and a right $\kappa$-action agreeing with the left one), and $\iota \colon V \to T'$ is an injective $T'$-linear map whose range is $\ker\pi$ viewed as a $T'$-submodule; thus $V \cong \ker\pi$.
--
--   The cover data: $\mathcal U$ is an `OrderedAffineCover` of $A_0$, that is, a finite linearly ordered index type $\mathcal U.\iota$ together with affine opens $\mathcal U.U_a$ whose supremum is $\top$. For $n \in \mathbb N$, $\mathcal U.\mathrm{Idx}\,n$ denotes the set of strictly monotone maps $s \colon \mathrm{Fin}(n+1) \to \mathcal U.\iota$, and $\mathcal U.\mathrm{inter}\,s = \bigwedge_j \mathcal U.U_{s(j)}$.
--
--   Local lifts: for each $a$ there are a scheme $Y_a$, a smooth morphism $q_a \colon Y_a \to \operatorname{Spec} T'$ (hypothesis `hq`) and a morphism $g_a \colon \mathcal U.U_a \to Y_a$ such that the square `hg` exhibits $g_a$, $(\mathcal U.U_a).\iota \gg f_0$, $q_a$, $\operatorname{Spec}(\pi)$ as a pullback; so $Y_a$ is a smooth lift of $\mathcal U.U_a$ over $T'$.
--
--   The special fibre: $f_k \colon A_k \to \operatorname{Spec}\kappa$ is separated, $L_k$ is a `RelativeGroupLaw` over $\kappa$ on $f_k$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec}\kappa$, with associativity, unit, inverse and naturality axioms), $i_0 \colon A_k \to A_0$ is an affine morphism and `hi₀` makes $i_0$, $f_k$, $f_0$, $\operatorname{Spec}(\rho)$ a pullback square. Further, $U_e \subseteq A_k$ is an affine open (`hUe`) through which the unit section factors: $e_1 \colon \operatorname{Spec}\kappa \to U_e$ satisfies $e_1$ followed by the inclusion of $U_e$ equals the underlying morphism of $L_k.\mathrm{one}(\mathrm{id})$.
--
--   The open-set bookkeeping: $O_a \colon A_0.\mathrm{Opens} \to (Y_a).\mathrm{Opens}$ for each $a$, subject to `hO` ($g_a^{-1}(O_a W) = (\mathcal U.U_a).\iota^{-1}(W)$), `hOm` (each $O_a$ is monotone), `hOtop` ($O_a(\mathcal U.U_a) = \top$), `hOinf` ($O_a W \wedge O_a W' \le O_a(W \wedge W')$) and `hOaff` ($O_a W$ is affine whenever $W$ is affine and $W \le \mathcal U.U_a$).
--
--   Chart identifications: for every $n$ and every $s \in \mathcal U.\mathrm{Idx}\,n$, $\sigma_s$ is a ring isomorphism $\kappa \otimes_{T'} \Gamma(Y_{s(0)}, O_{s(0)}(\mathcal U.\mathrm{inter}\,s)) \cong \Gamma(A_k, (\mathcal U.\mathrm{comap}\,i_0).\mathrm{inter}\,s)$, where $\mathcal U.\mathrm{comap}\,i_0$ is the ordered affine cover of $A_k$ with opens $i_0^{-1}(\mathcal U.U_a)$, and the $T'$-algebra structure on the sections of $Y_{s(0)}$ is the one induced by $q_{s(0)}$. Hypothesis `hσ₁` states that passing from the affine open $(\mathcal U.\mathrm{comap}\,i_0).\mathrm{inter}\,s$ to its spectrum, then along $\operatorname{Spec}(\sigma_s)$ and $\operatorname{Spec}$ of the right inclusion $\Gamma(Y_{s(0)}, O_{s(0)}(\cdot)) \to \kappa \otimes_{T'} \Gamma(Y_{s(0)}, O_{s(0)}(\cdot))$, and then along `fromSpec` of the affine open $O_{s(0)}(\mathcal U.\mathrm{inter}\,s)$, agrees with the composite of the inclusion of the triple-type overlap, the restriction of $i_0$ to $\mathcal U.\mathrm{inter}\,s$, the inclusion into $\mathcal U.U_{s(0)}$ and $g_{s(0)}$; hypothesis `hσ₂` states $\sigma_s(x \otimes 1) =$ the image of $x$ under the structure map $\kappa \to \Gamma(A_k, (\mathcal U.\mathrm{comap}\,i_0).\mathrm{inter}\,s)$ coming from $f_k$.
--
--   Overlap isomorphisms: for $a < b$, $\varphi_{ab}$ is an isomorphism of schemes $O_a(\mathcal U.U_a \wedge \mathcal U.U_b) \cong O_b(\mathcal U.U_a \wedge \mathcal U.U_b)$, subject to: `hφq`, that $\varphi_{ab}$ followed by the inclusion and $q_b$ equals the inclusion followed by $q_a$ (so $\varphi_{ab}$ is a morphism over $T'$); `hφg`, that there are morphisms $\gamma$, $\gamma'$ from $\mathcal U.U_a \wedge \mathcal U.U_b$ into the two opens inducing the restrictions of $g_a$ and of $g_b$ respectively, with $\gamma$ followed by $\varphi_{ab}$ equal to $\gamma'$ (so $\varphi_{ab}$ is the identity on the common locus downstairs); and `hφO`, that $\varphi_{ab}$ matches the $O$-parts: $\varphi_{ab}^{-1}\bigl((O_b(\cdot)).\iota^{-1}(O_b W)\bigr) = (O_a(\cdot)).\iota^{-1}(O_a W)$ for every open $W$ of $A_0$.
--
--   Triple overlaps: for each $r \in \mathcal U.\mathrm{Idx}\,2$, i.e. each triple $r(0) < r(1) < r(2)$, three isomorphisms $\rho^{ab}_r$, $\rho^{bc}_r$, $\rho^{ac}_r$ between the corresponding opens $O_{r(i)}(\mathcal U.\mathrm{inter}\,r)$ are given, and `hρab`, `hρbc`, `hρac` state that each is compatible with the corresponding $\varphi$: the square formed with the inclusions $O_{r(i)}(\mathcal U.\mathrm{inter}\,r) \le O_{r(i)}(\mathcal U.U_{r(i)} \wedge \mathcal U.U_{r(j)})$ commutes.
--
--   The obstruction cochain: $\omega$ lies in [`Algebra.PointDerivations`](def/Algebra_PointDerivations.html#L9) $\kappa$ $\Gamma(A_k, U_e)$ at the evaluation homomorphism attached to the unit point (the composite $U_e.\mathrm{topIso}^{-1}$, $e_1.\mathrm{appTop}$, $\Gamma\mathrm{Spec}$-iso), with values in $\kappa$-linear maps from $\mathrm{Hom}_\kappa(V,\kappa)$ to the Čech $2$-cochains of the cover $\mathcal U.\mathrm{comap}\,i_0$ with values in the structure-sheaf presheaf `OModulePresheaf.unit` $f_k$; that is, $\omega$ is a $\kappa$-linear map $D$ with $D(ab) = \mathrm{ev}(a)\cdot D(b) + \mathrm{ev}(b)\cdot D(a)$. Hypothesis `hω` identifies $\omega$ as the discrepancy between $\rho^{ac}_r$ and $\rho^{ab}_r$ followed by $\rho^{bc}_r$: for every triple $r$ there is a family $cs$ of $\kappa$-linear maps from $\mathrm{Hom}_\kappa(V,\kappa)$ to $\kappa \otimes_{T'} \Gamma(Y_{r(0)}, O_{r(0)}(\mathcal U.\mathrm{inter}\,r))$, indexed by sections in $\Gamma(A_k, U_e)$, such that the predicate `IsTangentCoordsOfPairAtVia` holds for $\ker\pi$, $V$, $\iota$, the ring $C = \Gamma(Y_{r(0)}, O_{r(0)}(\mathcal U.\mathrm{inter}\,r))$, the two morphisms $\operatorname{Spec} C \to Y_{r(2)}$ obtained from the inverse of the `isoSpec` of the affine open $O_{r(0)}(\mathcal U.\mathrm{inter}\,r)$ followed respectively by $\rho^{ac}_r$ and by $\rho^{ab}_r$ then $\rho^{bc}_r$, and then the inclusion of $O_{r(2)}(\mathcal U.\mathrm{inter}\,r)$, together with $f_k$, $L_k$, the open $i_0^{-1}(\mathcal U.U_{r(2)})$ with the morphism given by the restriction of $i_0$ followed by $g_{r(2)}$, the open $U_e$, and the family $cs$; by definition this predicate asserts the existence of a morphism $w_0$ from the spectrum of the thickening $(\kappa\otimes_{T'}C)\otimes_\kappa (\kappa \oplus V)$ into that open, lying over the canonical base morphism, and of $w_1$ from the same spectrum into $U_e$, such that $w_0$ followed by the given morphism is a tangent vector of the pair (in the sense of `IsTangentOfPair`: it factors through a morphism from the spectrum of the pair ring restricting to the two given morphisms along the two projections, via a Schlessinger map), $w_1$ followed by the inclusion of $U_e$ is the $L_k$-translate of $w_0$ to the unit, and $cs$ is the tangent-coordinate function of the induced ring homomorphism $\Gamma(A_k, U_e) \to$ thickening. Moreover $\sigma_r(cs\,a\,\xi) = \omega(a)(\xi)(r)$ for all $a \in \Gamma(A_k,U_e)$ and $\xi \in \mathrm{Hom}_\kappa(V,\kappa)$. Hypothesis `hωZ` states that $\omega$ is a cocycle: the Čech differential in degree $2$ kills $\omega(a)(\xi)$ for all $a$ and $\xi$.
--
--   Finally, $\eta$ is a point derivation of the same kind at the unit, with values in $\kappa$-linear maps from $\mathrm{Hom}_\kappa(V,\kappa)$ to the Čech $1$-cochains of $\mathcal U.\mathrm{comap}\,i_0$, and `hη` states that the Čech differential in degree $1$ sends $\eta(a)(\xi)$ to $\omega(a)(\xi)$ for all $a$ and $\xi$; that is, $\omega$ is the coboundary of $\eta$.
--
--   Under these hypotheses there exist: a new family of isomorphisms $\varphi'_{ab} \colon O_a(\mathcal U.U_a \wedge \mathcal U.U_b) \cong O_b(\mathcal U.U_a \wedge \mathcal U.U_b)$ for $a < b$; proofs `hφq'`, `hφg'`, `hφO'` that the new family satisfies exactly the three conditions imposed on $\varphi$ above, namely compatibility with $q_a$ and $q_b$, the existence for each $a<b$ of morphisms $\gamma_1$, $\gamma_2$ from $\mathcal U.U_a \wedge \mathcal U.U_b$ inducing the restrictions of $g_a$ and $g_b$ with $\gamma_1$ followed by $\varphi'_{ab}$ equal to $\gamma_2$, and the matching of the $O$-parts under preimages; new triple-overlap isomorphisms $\rho'^{ab}_r$, $\rho'^{bc}_r$, $\rho'^{ac}_r$ for every $r \in \mathcal U.\mathrm{Idx}\,2$; proofs `hρab'`, `hρbc'`, `hρac'` that each of these is compatible with the corresponding $\varphi'$ exactly as `hρab`, `hρbc`, `hρac` were for $\varphi$; and, as the final conjunct, the cocycle identity on every triple overlap: for all $r \in \mathcal U.\mathrm{Idx}\,2$,
--   $$(\rho'^{ac}_r)_{\mathrm{hom}} = (\rho'^{ab}_r)_{\mathrm{hom}} \text{ followed by } (\rho'^{bc}_r)_{\mathrm{hom}}.$$
--
--   This is the coboundary-correction step in the construction of a smooth lift of a smooth separated scheme along a small extension of Artinian local rings: once the obstruction $2$-cocycle attached to a system of local smooth lifts and overlap isomorphisms is known to be the Čech differential of a $1$-cochain of point derivations at the unit, the overlap isomorphisms can be replaced by ones still lying over $T'$, still inducing the identity downstairs and still respecting the chosen opens, whose triple-overlap restrictions satisfy the cocycle condition and hence glue. It is used in the proof of [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_smooth_isPullback_of_ker_mul_maximalIdeal_eq_bot_of_le_cechFinrank`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_smooth_isPullback_of_ker_mul_maximalIdeal_eq_bot_of_le_cechFinrank), the lifting statement for the Jacobian's abelian-scheme model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

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

    (η : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 1)))
    (hη : letI := algebraOfHom fk Ue
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fk).d (𝒰.comap i₀) 1 (η.1 a ξ) = ω.1 a ξ)
    :
    ∃ (φ' : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
      (hφq' : ∀ (a b : 𝒰.ι) (h : a < b),
        (φ' a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
      (hφg' : ∀ (a b : 𝒰.ι) (h : a < b),
        ∃ (γ₁ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
          (γ₂ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
          γ₁ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
          γ₂ ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
          γ₁ ≫ (φ' a b h).hom = γ₂)
      (hφO' : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
        (φ' a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)
      (ρab' : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
      (ρbc' : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
      (ρac' : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
      (hρab' : ∀ r : 𝒰.Idx 2,
        (ρab' r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
          (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
            (φ' (r.1 0) (r.1 1) (r.2 (by decide))).hom)
      (hρbc' : ∀ r : 𝒰.Idx 2,
        (ρbc' r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
          (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
            (φ' (r.1 1) (r.1 2) (r.2 (by decide))).hom)
      (hρac' : ∀ r : 𝒰.Idx 2,
        (ρac' r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
          (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
            (φ' (r.1 0) (r.1 2) (r.2 (by decide))).hom),
      ∀ r : 𝒰.Idx 2, (ρac' r).hom = (ρab' r).hom ≫ (ρbc' r).hom := by sorry
