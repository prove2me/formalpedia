-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_quasiCompact_comp_of_isClosedImmersion_iff_qmConditions
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.quasiCompact_comp_of_isClosedImmersion_iff_qmConditions
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/869f3690-a870-5e42-aba3-1a453c4d142c
-- title:
--   Quasi-compactness of the QM locus over the base
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($a>0$ or $b>0$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x$, and let $\beta:\mathrm{Fin}(2\cdot 2)\to\Lambda$ be a $\mathbb{Z}$-basis of $\Lambda$ (each $x\in\Lambda$ is uniquely $\sum_j c_j\beta_j$ with $c_j\in\mathbb{Z}$). Let $d,m\in\mathbb{N}$ with $m\ge 3$, let $R$ be a commutative ring in which $m$ is invertible, and let $X$ be a polarised abelian scheme of relative dimension $2$, polarisation degree $d$ and full level $m$ over $R$. Let $\pi_E:E\to\operatorname{Spec}R$ be a morphism and let $\mathrm{cl}$ assign, to every ring map $\varphi:R\to R'$, every relative group law $L'$ on $f':A'\to\operatorname{Spec}R'$ together with $g:A'\to X.A$ exhibiting $(f',L')$ as the pullback of $(X.f,X.L)$ along $\varphi$, and every action of $\Lambda$ on $(f',L')$, a point of $E$ over $\operatorname{Spec}\varphi$; assume `RepresentsLatticeActions` holds for $\mathrm{cl}$ (compatibility with further base change, and bijectivity of $\mathrm{cl}$ on $\Lambda$-actions for each base-change datum), and that $\pi_E$ is separated, locally of finite type and locally of finite presentation. Assume further that for every $e:\mathrm{Fin}(2\cdot 2)\to\mathbb{N}$ there is an open $U\subseteq E$ with $U$ closed and $U\hookrightarrow E\to\operatorname{Spec}R$ quasi-compact, such that for every base-change datum and every $\Lambda$-action $X'$ the image of $\mathrm{cl}$ lies in $U$ precisely when, for each $j$ and each geometric point $s_k:R'\to k$ with $k$ algebraically closed, the geometric fibre $H^0$-rank of $g^{*}X.\mathrm{pol}\otimes X'.\mathrm{act}(\beta_j)^{*}g^{*}X.\mathrm{pol}$ equals $e_j$. Finally let $\iota:Z\to E$ be a closed immersion such that, for every base-change datum and $\Lambda$-action $i'$, the point $\mathrm{cl}(i')$ factors through $\iota$ if and only if the following three conditions hold: (i) for every algebraically closed $k$ with $s_k:R'\to k$, every finite-dimensional $k$-space $V$ injectively parametrising, by $\tau$, exactly the tangent vectors of $L'$ at the identity, additively and $k$-linearly compatibly with $L'$, every $x\in\Lambda$ and every $k$-linear $\Phi$ on $V$ induced by $i'.\mathrm{act}(x)$ through $\tau$, and every integer $n$ with $x+\bar{x}=n$, the trace of $\Phi$ is $n$ in $k$; (ii) there is a section $P$ of $f'$ with $i'.\mathrm{act}(\beta_j)\circ P$ followed by $g$ equal to $\operatorname{Spec}\varphi$ followed by the $j$-th level point $X.P_j$, for all $j$; (iii) there is a module $\mathrm{polE}$ on $A'$ which is canonical polarisation data for $(f',L',i'.\mathrm{act},\mathrm{star})$ and such that $g^{*}X.\mathrm{pol}$ and $\mathrm{polE}\otimes\mathrm{polE}\otimes\mathrm{polE}$ are locally isomorphic over the base. Then $\iota$ followed by $\pi_E$ is quasi-compact.
--
--   This supplies the quasi-compactness half of the finiteness properties of the locus of quaternionic-multiplication structures inside the scheme representing $\Lambda$-actions on the polarised abelian surface $X$: the degree pieces of $E$ are quasi-compact over $\operatorname{Spec}R$, and the QM locus $Z$ lands in a single such piece because the intersection degrees $h^0(\mathcal{L}\otimes i(\beta_j)^{*}\mathcal{L})$ are the same for every QM structure. It is used in the construction of the Čerednik–Drinfeld/Shimura-curve moduli scheme, namely by the representability statement [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_represents_of_representsLatticeActions_of_isUnit_two`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_represents_of_representsLatticeActions_of_isUnit_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_quasiCompact_comp_of_isClosedImmersion_iff_qmConditions.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_CerednikDrinfeld_QMLatticeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem AlgebraicGeometry.PolarisedAbelianScheme.quasiCompact_comp_of_isClosedImmersion_iff_qmConditions
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (R : Type) [CommRing R] (hm' : IsUnit ((m : ℕ) : R)) (X : PolarisedAbelianScheme 2 d m R)
    (E : Scheme.{0}) (πE : E ⟶ Spec (CommRingCat.of R))
    (cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A), IsGroupPullback φ X.L L' g →
        LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE)
    (hE : RepresentsLatticeActions Λ X.L E πE cl) (hEsep : IsSeparated πE) (hElft : LocallyOfFiniteType πE)
    (hElfp : LocallyOfFinitePresentation πE)
    (hEpieces : (∀ e : Fin (2 * 2) → ℕ, ∃ U : E.Opens, IsClosed (U : Set E) ∧ QuasiCompact (U.ι ≫ πE) ∧
        ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
          (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A) (hg : IsGroupPullback φ X.L L' g) (X' : LatticeAction Λ f' L'),
          (Set.range (cl R' φ L' g hg X').1.base ⊆ (U : Set E) ↔
            ∀ (j : Fin (2 * 2)) (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k),
              Scheme.Modules.geomFibreH0Finrank f'
                ((Scheme.Modules.pullback g).obj X.pol ⊗
                  (Scheme.Modules.pullback (X'.act (β j))).obj ((Scheme.Modules.pullback g).obj X.pol)) k sk = e j)))
    (Z : Scheme.{0}) (ι : Z ⟶ E) (hι : IsClosedImmersion ι)
    (hZ : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A) (hg : IsGroupPullback φ X.L L' g) (i' : LatticeAction Λ f' L'),
        ((∃ y : Spec (CommRingCat.of R') ⟶ Z, y ≫ ι = (cl R' φ L' g hg i').1) ↔
          ((∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k)
              (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f'),
              Function.Injective τ →
              (∀ P : SchemeHomOver (tangentBase k sk) f', P ∈ Set.range τ ↔ IsTangentVector L' k sk P) →
              (∀ v w : V, τ (v + w) = L'.mul (tangentBase k sk) (τ v) (τ w)) →
              (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
              ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
              ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
                LinearMap.trace k V Φ = (n : k)) ∧
          (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) f',
            ∀ j : Fin (2 * 2), (pushPt (i'.act (β j)) (i'.act_over (β j)) P).1 ≫ g =
              Spec.map (CommRingCat.ofHom φ) ≫ (X.P j).1) ∧
          (∃ polE : A'.Modules, CerednikDrinfeld.QM.IsCanonicalPolData f' L' i'.act i'.act_over star polE ∧
              LocIsoOnBase f' ((Scheme.Modules.pullback g).obj X.pol) (polE ⊗ polE ⊗ polE))))) :
    QuasiCompact (ι ≫ πE) := by sorry
