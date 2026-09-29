-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/a461a6d4-ab09-58d4-8a3c-5f9a392145d2
-- title:
--   Exactly intertwined germs of padded isogenies on nilpotent points
-- statement:
--   Fix a prime $r$ and $N \neq 0$ with $r \nmid N$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $Onr$, rationals $a,b$, and a $\mathbb Z$-submodule $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ which is an order maximal among orders and contains every rational integer; fix $coord : \Lambda \to \mathbb{Z}_{r}^{(2)} \times \mathbb{Z}_{r}^{(2)}$ satisfying `IsOrderCoord` (additive, sending $1$ to $(1,0)$, multiplicative for the twisted law built from $r$ and the Witt-vector Frobenius, injective, with dense image and the trace compatibility), and a fake elliptic curve $A_0$ with level-$N$ data over $Onr/(\pi)$. Let $k$ be an algebraically closed $\mathcal O$-algebra in which $\pi$ and $r$ are nilpotent, $\psi : Onr \to k$ an $\mathcal O$-algebra map, and $x = (E,\rho)$, $x' = (E',\rho')$ rigidified curves over $(k,\psi)$, so each carries reductions $E_b$, $A_b$ over $k/(\pi)$, maps $g_b$, $g_A$ exhibiting them as pullbacks of $E$ and of $A_0$ (the latter along `residueLeg` $\pi\,\psi$), and a level-preserving isogeny pair $\varphi, \varphi'$ of degree $r^{d}$. Let $X, X'$ be formal $\mathcal O_D$-modules over $k$, $\theta, \theta'$ two-dimensional formal coordinates for the structure maps of $E$, $E'$, and $T_0 : X \to X'$ a homomorphism. Assume: $X_0, \theta_0$ make $A_0$ a formal module via $coord$; $\theta_A$ makes $A_b$ a formal module via $coord$ and the base change of $X_0$ along `residueLeg`, with $(\theta_A)\ {\gg}\ g_A = \theta_0$ on nilpotent points over rings carrying compatible $Onr/(\pi)$- and $k/(\pi)$-structures; $\theta_E, \theta_{E'}$ make $E_b, E'_b$ formal modules via the reductions of $X, X'$ modulo $\pi$, with $(\theta_E)\ {\gg}\ g_b = \theta$ and $(\theta_{E'})\ {\gg}\ g'_b = \theta'$; $v : A_b \to A'_b$ exhibits $A_b$ as the pullback of $A'_b$ along the identity of $k/(\pi)$ and satisfies $v \gg g'_A = g_A$. Let $\kappa$ and $\kappa_B$ be ring maps from $Onr/(\pi)$ to $Onr/(r)$ and from $k/(\pi)$ to $k/(r)$, with $\kappa_B$ compatible with the two quotient maps on $k$ and with $\kappa$ through `residueLeg` and `residueMap` $\psi$. Let $\sigma, \sigma'$ be pairs of two-variable power series over $k/(\pi)$ with vanishing constant terms which represent $\varphi' \gg g_b$ and $\varphi'' \gg g'_b$ in the sense that, over any ring $B''$ algebra over $k/(\pi)$, over $k$ and over $Onr/(\pi)$ with the structure maps factoring as prescribed, for any ideal $J$ with $J^{m+1} = 0$, any $s$ with entries in $J$ and any $B''$-point $P_A$ of $A_b$ over $\operatorname{Spec}(k/(\pi))$ with $P_A \gg g_A = \theta_0(s)$, one has $P_A \gg \varphi' \gg g_b = \theta(\mathrm{nilEval}_m(\sigma)(s))$, and likewise for $x'$. Finally let $c_0, c, c'$ be natural numbers such that, after reduction modulo $r$, the composites of series $[r^{c}]_{X'} \circ \bar T_0 \circ \bar\sigma \circ [r^{c_0}]$ and $[r^{c'}]_{X'} \circ \bar\sigma' \circ [r^{c_0}]$ agree, the outer right factor being the $r^{c_0}$-action on $X_0$ transported to $k/(r)$. Then there exist pairs of series $\sigma_1, \sigma_1'$ over $k/(\pi)$ with vanishing constant terms such that for every $(k/(\pi))$-algebra $B''$, every ideal $J$ with $J^{n+1} = 0$ and every $s : \mathrm{Fin}\,2 \to J$ one has $\theta_A(s) \gg \big([r^{c_0}]_{A_b} \gg \varphi' \gg [r^{c}]_{E_b}\big) = \theta_E(\mathrm{nilEval}_n(\sigma_1)(s))$ and $\theta_A(s) \gg \big([r^{c_0}]_{A_b} \gg v \gg \varphi'' \gg [r^{c'}]_{E'_b}\big) = \theta_{E'}(\mathrm{nilEval}_n(\sigma_1')(s))$, where the bracket maps are the actions of the integers $r^{c_0}, r^{c}, r^{c'}$ of $\Lambda$, and moreover the reduction of $T_0$ modulo $\pi$ intertwines them exactly: $\bar T_0 \circ \sigma_1 = \sigma_1'$ over $k/(\pi)$.
--
--   This is a step in the Čerednik–Drinfeld comparison of rigidified fake elliptic curves: germs of the two padded quasi-isogenies $[r^{c_0}] \gg \varphi' \gg [r^{c}]$ and $[r^{c_0}] \gg v \gg \varphi'' \gg [r^{c'}]$, which by hypothesis are intertwined by $T_0$ only after reduction modulo $r$, are replaced by germs intertwined exactly over $k/(\pi)$, and the representation clauses are simultaneously freed of the auxiliary algebra-structure compatibilities. It feeds the construction of an isomorphism of rigidified curves from a formal isomorphism over an algebraically closed base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (hkr : IsNilpotent ((r : ℕ) : k))
    (ψ : Onr →ₐ[𝒪] k)
    (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ k ψ)
    (X X' : FormalODModule r k)
    (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2)
    (T₀ : FormalODModule.Hom X X')

    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (θA : RelativeGroupLaw.FormalCoordinates x.2.Ab.f 2)
    (hθA : x.2.Ab.IsFormalModuleVia coord (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) θA)
    (hθAg : ∀ (B'' : Type) [CommRing B''] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''],
      algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
      ∀ (s : Fin 2 → B''), (∀ i, IsNilpotent (s i)) → (θA B'' s).1 ≫ x.2.gA = (θ₀ B'' s).1)

    (θE : RelativeGroupLaw.FormalCoordinates x.2.Eb.f 2) (θE' : RelativeGroupLaw.FormalCoordinates x'.2.Eb.f 2)
    (hθE : x.2.Eb.IsFormalModuleVia coord (X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) θE)
    (hθE' : x'.2.Eb.IsFormalModuleVia coord (X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) θE')
    (hθEg : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'']
      [IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (s : Fin 2 → B''),
      (∀ i, IsNilpotent (s i)) → (θE B'' s).1 ≫ x.2.gb = (θ B'' s).1)
    (hθEg' : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'']
      [IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (s : Fin 2 → B''),
      (∀ i, IsNilpotent (s i)) → (θE' B'' s).1 ≫ x'.2.gb = (θ' B'' s).1)

    (v : x.2.Ab.A ⟶ x'.2.Ab.A) (hv : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x'.2.Ab x.2.Ab v) (hvg : v ≫ x'.2.gA = x.2.gA)

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (κB : (k ⧸ Ideal.span {algebraMap 𝒪 k π}) →+* (k ⧸ pIdeal r k))
    (hκB : κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) = Ideal.Quotient.mk (pIdeal r k))
    (hκB' : κB.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) = (residueMap (ψ : Onr →+* k)).comp κ)
    (σ σ' : Series (k ⧸ Ideal.span {algebraMap 𝒪 k π}))
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (hσ : (∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] [Algebra k B''] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap k B'' = (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ x.2.Ab.A,
            PA ≫ x.2.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'')) →
            PA ≫ x.2.gA = (θ₀ B'' s).1 →
              PA ≫ x.2.φ' ≫ x.2.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1))
    (hσ' : (∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] [Algebra k B''] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap k B'' = (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ x'.2.Ab.A,
            PA ≫ x'.2.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'')) →
            PA ≫ x'.2.gA = (θ₀ B'' s).1 →
              PA ≫ x'.2.φ' ≫ x'.2.gb = (θ' B'' (fun i => MvFormalGroup.nilEval m (σ' i) s)).1))
    (c₀ c c' : ℕ)
    (heq : (((X'.map (Ideal.Quotient.mk (pIdeal r k))).act ((r : Zp2 r) ^ c)).comp
          ((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r k))).comp (σ.map κB))).comp
        (((X₀.map κ).map (residueMap (ψ : Onr →+* k))).act ((r : Zp2 r) ^ c₀)) =
      (((X'.map (Ideal.Quotient.mk (pIdeal r k))).act ((r : Zp2 r) ^ c')).comp (σ'.map κB)).comp
        (((X₀.map κ).map (residueMap (ψ : Onr →+* k))).act ((r : Zp2 r) ^ c₀))) :
    ∃ σ₁ σ₁' : Series (k ⧸ Ideal.span {algebraMap 𝒪 k π}),
      (∀ i, MvPowerSeries.constantCoeff (σ₁ i) = 0) ∧ (∀ i, MvPowerSeries.constantCoeff (σ₁' i) = 0) ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θA B'' s).1 ≫ (x.2.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ x.2.φ' ≫ x.2.Eb.act ⟨(((r ^ c : ℕ) : ℤ) : ℚ), hΛℤ _⟩) =
            (θE B'' (fun i => MvFormalGroup.nilEval n (σ₁ i) s)).1) ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θA B'' s).1 ≫ (x.2.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ v ≫ x'.2.φ' ≫ x'.2.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) =
            (θE' B'' (fun i => MvFormalGroup.nilEval n (σ₁' i) s)).1) ∧
      (T₀.toSeries.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).comp σ₁ = σ₁' := by sorry
