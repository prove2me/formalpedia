-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_inducing_of_iso_reduction_of_act_pow_comp_eq_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_inducing_of_iso_reduction_of_act_pow_comp_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/51054434-7655-5b25-851e-328dfdc7f219
-- title:
--   Lifting an isomorphism of reductions of rigidified fake elliptic curves
-- statement:
--   Fix a prime $r$ and a nonzero $N$ with $r \nmid N$, a commutative ring $\mathcal{O}$ with an element $\pi$, an $\mathcal{O}$-algebra $Onr$, and a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order (an order, and maximal among orders) containing every rational integer; fix $coord : \Lambda \to \mathbb{Z}_{r^2} \times \mathbb{Z}_{r^2}$ satisfying `IsOrderCoord` (additive, $1 \mapsto (1,0)$, multiplicative for the twisted rule involving $r$ and the Witt-vector Frobenius, injective, with dense image and the prescribed trace condition), and a fake elliptic curve $A_0$ with $\Lambda$-action and level $N$ over $Onr/(\pi)$. Let $k$ be an algebraically closed field which is an $\mathcal{O}$-algebra with $\pi$ and $r$ nilpotent in $k$, let $\psi : Onr \to k$ be an $\mathcal{O}$-algebra map, and let $x = (E,\rho)$, $x' = (E',\rho')$ be rigidified curves over $(k,\psi)$: each carries a reduction $E_b$ over $k/(\pi)$ with comparison $g_b$, a curve $A_b$ over $k/(\pi)$ with $g_A$ to $A_0$, an exponent $d$ and an $r^d$-isogeny pair $\varphi, \varphi'$ between $E_b$ and $A_b$ preserving the level. Let $X, X'$ be formal $\mathcal{O}_D$-modules over $k$ (a two-dimensional commutative formal group with $\mathbb{Z}_{r^2}$-action and uniformiser series), $\theta, \theta'$ two-dimensional formal coordinates for $E, E'$ exhibiting them as formal modules for $X, X'$ via $coord$, and $T_0 : X \to X'$ a homomorphism of formal $\mathcal{O}_D$-modules. Assume further: formal coordinates $\theta_E, \theta_{E'}$ exhibiting $E_b, E'_b$ as formal modules for the reductions of $X, X'$ over $k/(\pi)$ and compatible with $\theta, \theta'$ through $g_b, g'_b$ on nilpotent points; mutually inverse morphisms $u_A : A'_b \to A_b$ and $v : A_b \to A'_b$, each a pullback comparison along the identity of $k/(\pi)$ (so compatible with group laws, $\Lambda$-actions and level) and commuting with $g_A$, $g'_A$; natural numbers $c_0, c, c'$; and an isomorphism $e : E_b \cong E'_b$ over $k/(\pi)$ compatible with the group laws and the $\Lambda$-actions, inducing the reduction of $T_0$ on formal points in the coordinates $\theta_E, \theta_{E'}$, and satisfying $\bigl([r^{c_0}]_{A_b} \gg \varphi' \gg [r^{c}]_{E_b}\bigr) \gg e = [r^{c_0}]_{A_b} \gg v \gg \varphi'' \gg [r^{c'}]_{E'_b}$ in diagrammatic order. Then there is an isomorphism $i : E \cong E'$ over $k$ with $i \gg f' = f$ satisfying `IsoVia` (it transports the relative group law, commutes with the $\Lambda$-action, and a point factors through the level structure of $E$ precisely when its image factors through that of $E'$), inducing $T_0$ on formal points: for every $k$-algebra $B''$, ideal $J$ with $J^{n+1} = 0$ and tuple $s$ in $J$, $(\theta\,B''\,s) \gg i = \theta'\,B''\,(\mathrm{nilEval}\ n\ (T_0)\ s)$; moreover there exist $i_b : E_b \to E'_b$ with $i_b \gg g'_b = g_b \gg i$ and $i_b$ over $k/(\pi)$, a pullback comparison $u : A'_b \to A_b$ along the identity with $u \gg g_A = g'_A$, and natural numbers $i_1, j_1$ with $i_b \gg \varphi'' \gg u \gg [r^{i_1}]_{A_b} = \varphi \gg [r^{j_1}]_{A_b}$.
--
--   This is the rigidity step of the Čerednik–Drinfeld comparison: an isomorphism between the reductions modulo $\pi$ of two rigidified fake elliptic curves over an algebraically closed base, inducing a prescribed homomorphism of the associated formal $\mathcal{O}_D$-modules and compatible with the base-point data up to $r$-power scalars, descends to an isomorphism of the curves themselves inducing that homomorphism, with the rigidifications matching up to $r$-power scalars. It feeds the statement [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isoVia_corr_inducing_of_formalIso_of_isRigTransport_of_isAlgClosed), where the isomorphism of reductions is produced from a formal datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_inducing_of_iso_reduction_of_act_pow_comp_eq_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_inducing_of_iso_reduction_of_act_pow_comp_eq_of_isAlgClosed
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
    (hX : x.1.IsFormalModuleVia coord X θ) (hX' : x'.1.IsFormalModuleVia coord X' θ')
    (T₀ : FormalODModule.Hom X X')

    (θE : RelativeGroupLaw.FormalCoordinates x.2.Eb.f 2) (θE' : RelativeGroupLaw.FormalCoordinates x'.2.Eb.f 2)
    (hθE : x.2.Eb.IsFormalModuleVia coord (X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) θE)
    (hθE' : x'.2.Eb.IsFormalModuleVia coord (X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) θE')
    (hθEg : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'']
      [IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (s : Fin 2 → B''),
      (∀ i, IsNilpotent (s i)) → (θE B'' s).1 ≫ x.2.gb = (θ B'' s).1)
    (hθEg' : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'']
      [IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (s : Fin 2 → B''),
      (∀ i, IsNilpotent (s i)) → (θE' B'' s).1 ≫ x'.2.gb = (θ' B'' s).1)

    (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (huAg : uA ≫ x.2.gA = x'.2.gA)
    (v : x.2.Ab.A ⟶ x'.2.Ab.A) (hv : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x'.2.Ab x.2.Ab v) (hvg : v ≫ x'.2.gA = x.2.gA)
    (huv : uA ≫ v = 𝟙 _) (hvu : v ≫ uA = 𝟙 _)

    (c₀ c c' : ℕ)
    (e : x.2.Eb.A ≅ x'.2.Eb.A) (he : e.hom ≫ x'.2.Eb.f = x.2.Eb.f)
    (hαe : (x.2.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ x.2.φ' ≫ x.2.Eb.act ⟨(((r ^ c : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ e.hom =
      x.2.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ v ≫ x'.2.φ' ≫ x'.2.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hemul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) (P Q : SchemeHomOver t x.2.Eb.f),
      mapPt e.hom he (x.2.Eb.L.mul t P Q) = x'.2.Eb.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (heact : ∀ y : ↥Λ, x.2.Eb.act y ≫ e.hom = e.hom ≫ x'.2.Eb.act y)
    (heT : ∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ l, s l ∈ J) →
        (θE B'' s).1 ≫ e.hom =
          (θE' B'' (fun l => MvFormalGroup.nilEval n ((T₀.toSeries.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) l) s)).1) :
    ∃ (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f), FakeEllipticCurve.IsoVia x.1 x'.1 i hi ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ l, s l ∈ J) →
            (θ B'' s).1 ≫ i.hom = (θ' B'' (fun l => MvFormalGroup.nilEval n (T₀.toSeries l) s)).1) ∧

      ∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
        (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
        (i₁ j₁ : ℕ),
        ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
