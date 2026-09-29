-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_map_hom_comp_germ_eq_germ_of_act_pow_comp_map_comp_act_pow_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.map_hom_comp_germ_eq_germ_of_act_pow_comp_map_comp_act_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/2aaa8069-f70c-5dc3-b51c-3b772225c19b
-- title:
--   Descending a cancelled germ identity from k/(r) to k/(π)
-- statement:
--   Fix a prime $r$ and $N \neq 0$ with $r \nmid N$, a commutative ring $\mathcal{O}$ with an element $\pi$, and an $\mathcal{O}$-algebra $Onr$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order and contains every rational integer, and let $coord : \Lambda \to \mathrm{Zp2}\,r \times \mathrm{Zp2}\,r$ satisfy `IsOrderCoord`: additive, sending $1$ to $(1,0)$, multiplicative for the twisted rule on $W(\mathbb{F}_{r^2})^2$ involving the Witt-vector Frobenius, injective, with dense image modulo all powers of $r$, and matching reduced traces. Let $A_0$ be a fake elliptic curve over $Onr/(\pi)$, let $k$ be an algebraically closed $\mathcal{O}$-algebra field in which $\pi$ and $r$ are nilpotent, let $\psi : Onr \to k$ be an $\mathcal{O}$-algebra map, and let $x, x'$ be rigidified curves over $k$ relative to $A_0$ and $\psi$; so each carries legs $\mathrm{Eb}, \mathrm{Ab}$ over $k/(\pi)$ together with $g_b$, $g_A$, and isogenies $\varphi, \varphi'$. Let $X, X'$ be formal $\mathcal{O}_D$-modules over $k$, let $T_0 : X \to X'$ be a homomorphism of such, let $\theta, \theta'$ be two-dimensional relative formal coordinates on the structure morphisms of the curves underlying $x, x'$, and let $X_0, \theta_0$ exhibit $A_0$ as a formal module via $coord$. Further hypotheses, summarised here, record: that $\theta_A$ exhibits $x.2.\mathrm{Ab}$ as a formal module via $coord$ for $X_0$ base-changed along `residueLeg` $\pi\,\psi$, and is carried to $\theta_0$ by $g_A$; that $\theta_E, \theta_{E'}$ exhibit the $\mathrm{Eb}$ legs as formal modules for $X, X'$ reduced to $k/(\pi)$, and are carried to $\theta, \theta'$ by the respective $g_b$; a morphism $v$ between the $\mathrm{Ab}$ legs that is a pullback along the identity and satisfies $v$ followed by $x'.2.g_A$ equals $x.2.g_A$; bridge maps $\kappa : Onr/(\pi) \to Onr/(r)$ and $\kappa_B : k/(\pi) \to k/(r)$ compatible with the quotient maps and with the legs; and series $\sigma, \sigma'$ over $k/(\pi)$ with vanishing constant terms which, for every base ring $B''$ compatibly an algebra over $k$, $k/(\pi)$ and $Onr/(\pi)$, every ideal $J$ with $J^{m+1} = 0$ and every $s$ with entries in $J$, compute the composite of a $B''$-point $P_A$ of the $\mathrm{Ab}$ leg with $\varphi'$ and $g_b$ as $\theta$ (respectively $\theta'$) evaluated at the truncated substitutions $\mathrm{nilEval}\,m\,\sigma_i\,s$, whenever $P_A$ lies over $B''$ and $P_A$ followed by $g_A$ equals $\theta_0(s)$. Given natural numbers $c_0, c, c'$ such that, after base change to $k/(r)$, the identity $[r^{c}]_{X'} \circ T_0 \circ \sigma \circ [r^{c_0}] = [r^{c'}]_{X'} \circ \sigma' \circ [r^{c_0}]$ of series holds, where $[r^{c_0}]$ is the action of $r^{c_0} \in \mathrm{Zp2}\,r$ on $X_0$ reduced along $\kappa$ and then along the residue map of $\psi$, the conclusion is the corresponding identity over $k/(\pi)$: $T_0$ reduced to $k/(\pi)$ composed with $[r^{c}]_{X} \circ \sigma \circ [r^{c_0}]$ equals $[r^{c'}]_{X'} \circ \sigma' \circ [r^{c_0}]$, the actions now being taken on $X, X'$ reduced to $k/(\pi)$ and on $X_0$ transported along `residueLeg` $\pi\,\psi$.
--
--   This is the power-series half of the germ-exactness step in the Čerednik–Drinfeld description of fake elliptic curves with nilpotent $\pi$: an identity between transported germs is verified modulo $r$, where the formal $\mathcal{O}_D$-module data are rigid, and then descended to the ring $k/(\pi)$ on which the germs actually live. It is used in the proof of [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_map_hom_comp_germ_eq_germ_of_act_pow_comp_map_comp_act_pow_eq.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.map_hom_comp_germ_eq_germ_of_act_pow_comp_map_comp_act_pow_eq
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
    (T₀.toSeries.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).comp
        (((X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c)).comp
          (σ.comp ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀)))) =
      ((X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c')).comp
        (σ'.comp ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀))) := by sorry
