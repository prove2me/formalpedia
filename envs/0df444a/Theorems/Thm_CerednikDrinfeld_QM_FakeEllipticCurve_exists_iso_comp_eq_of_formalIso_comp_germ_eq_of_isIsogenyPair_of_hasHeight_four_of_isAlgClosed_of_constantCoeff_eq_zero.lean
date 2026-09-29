-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_iso_comp_eq_of_formalIso_comp_germ_eq_of_isIsogenyPair_of_hasHeight_four_of_isAlgClosed_of_constantCoeff_eq_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_iso_comp_eq_of_formalIso_comp_germ_eq_of_isIsogenyPair_of_hasHeight_four_of_isAlgClosed_of_constantCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/5f9e815a-1380-5cfe-a3a5-4fc393482459
-- title:
--   Formal mathcal O_D-isomorphism of germs induces isomorphism of targets
-- statement:
--   Fix $a,b\in\mathbb Q$, an additive subgroup $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ containing $1$ and all rational integers, an integer $N$, and a prime $r$. Let $\mathrm{coord}:\Lambda\to W(\mathbb F_{r^2})^2\times W(\mathbb F_{r^2})^2$ satisfy `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, is multiplicative in the twisted sense $\mathrm{coord}(mm')=(m_1m'_1+r\,m_2\varphi(m'_2),\,m_1m'_2+m_2\varphi(m'_1))$, is injective, has dense image modulo every power of $r$, and computes reduced traces. Let $k$ be an algebraically closed field in which $r$ is nilpotent. Let $A$, $E$, $E'$ be fake elliptic curves over $k$ for the data $(\Lambda,N)$, let $X_A$, $X$, $X'$ be formal $\mathcal O_D$-modules of dimension $2$ over $k$ (commutative formal group laws with $W(\mathbb F_{r^2})$-action and a $\varpi$ with $\varpi\circ\varpi=[r]$ and $\varpi\circ[a]=[\varphi(a)]\circ\varpi$), and let $\theta_A,\theta,\theta'$ be $2$-parameter formal coordinates on $A$, $E$, $E'$ exhibiting these formal modules via $\mathrm{coord}$: each $\theta$ parameterises the infinitesimal points of the relative group law bijectively and additively, and transports the $\Lambda$-action to $\mathrm{act}(\mathrm{coord}(m)_1)+_{F}\mathrm{act}(\mathrm{coord}(m)_2)\circ\varpi$. Assume $X_A$ has height $4$, i.e. the kernel of multiplication by $r$ on $X_A$ has degree $r^4$. Let $\alpha:A\to E$, $\check\alpha:E\to A$ and $\alpha':A\to E'$, $\check\alpha':E'\to A$ be isogeny pairs of degrees $r^d$, $r^{d'}$: morphisms over $\operatorname{Spec}k$, homomorphisms for the group laws, commuting with the $\Lambda$-actions, whose two composites are the action of $r^d$ (respectively $r^{d'}$). Let $\sigma,\sigma':(\mathbb F$-indexed) pairs of power series in two variables over $k$ with zero constant term be germs of $\alpha$ and $\alpha'$ in these coordinates: for every $k$-algebra $B$, every ideal $J$ with $J^{n+1}=0$ and every $s$ with entries in $J$, the point $\theta_A(s)$ followed by $\alpha$ is $\theta(\sigma(s))$, and likewise for $\alpha'$, $\theta'$, $\sigma'$, where substitution is evaluated by truncation. Finally let $T_0:X\to X'$ be a homomorphism of formal $\mathcal O_D$-modules admitting a two-sided inverse, with $T_0\circ\sigma=\sigma'$. The conclusion is that there exists an isomorphism $e:E\xrightarrow{\sim}E'$ of schemes with $e$ followed by the structure morphism of $E'$ equal to that of $E$, such that $\alpha$ followed by $e$ equals $\alpha'$, such that $e$ carries the group law of $E$ to that of $E'$ on points over any base, such that $E.\mathrm{act}(x)$ followed by $e$ equals $e$ followed by $E'.\mathrm{act}(x)$ for all $x\in\Lambda$, and such that $e$ induces $T_0$ on germs: $\theta(s)$ followed by $e$ equals $\theta'(T_0(s))$ for all nilpotent test data as above. No compatibility with the remaining level-$N$ data of $E$ and $E'$ is asserted.
--
--   This is the rigidity step in the Čerednik–Drinfeld description of the supersingular locus: for a fake elliptic curve whose formal module has maximal height $4$, all $r$-power torsion is infinitesimal, so an $r$-power isogeny is determined by its germ, and an isomorphism of germs commuting with the $\mathcal O_D$-structure descends to an isomorphism of the isogeny targets respecting group law and quaternionic action. It feeds the construction of the isomorphism of moduli data used in `exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_iso_comp_eq_of_formalIso_comp_germ_eq_of_isIsogenyPair_of_hasHeight_four_of_isAlgClosed_of_constantCoeff_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_iso_comp_eq_of_formalIso_comp_germ_eq_of_isIsogenyPair_of_hasHeight_four_of_isAlgClosed_of_constantCoeff_eq_zero
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (hΛ1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] [IsAlgClosed k] (hkr : IsNilpotent ((r : ℕ) : k))

    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA) (hA4 : XA.HasHeight 4)

    (E E' : FakeEllipticCurve Λ N k) (X X' : FormalODModule r k)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2)
    (hX : E.IsFormalModuleVia coord X θ) (hX' : E'.IsFormalModuleVia coord X' θ')

    (d d' : ℕ) (α : A.A ⟶ E.A) (αv : E.A ⟶ A.A) (hα : FakeEllipticCurve.IsIsogenyPair (r ^ d) A E α αv)
    (α' : A.A ⟶ E'.A) (αv' : E'.A ⟶ A.A) (hα' : FakeEllipticCurve.IsIsogenyPair (r ^ d') A E' α' αv')

    (σ σ' : Series k) (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (hσ : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (θA B'' s).1 ≫ α = (θ B'' (fun i => MvFormalGroup.nilEval n (σ i) s)).1)
    (hσ' : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (θA B'' s).1 ≫ α' = (θ' B'' (fun i => MvFormalGroup.nilEval n (σ' i) s)).1)

    (T₀ : FormalODModule.Hom X X') (hT₀ : T₀.IsIso) (hTσ : T₀.toSeries.comp σ = σ') :
    ∃ (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f),
      α ≫ e.hom = α' ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
        mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ B'' s).1 ≫ e.hom = (θ' B'' (fun i => MvFormalGroup.nilEval n (T₀.toSeries i) s)).1) := by sorry
