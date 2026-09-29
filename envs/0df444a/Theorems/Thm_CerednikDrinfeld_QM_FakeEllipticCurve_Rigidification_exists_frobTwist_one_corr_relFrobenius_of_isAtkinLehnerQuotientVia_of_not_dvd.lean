-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_frobTwist_one_corr_relFrobenius_of_isAtkinLehnerQuotientVia_of_not_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_frobTwist_one_corr_relFrobenius_of_isAtkinLehnerQuotientVia_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/e5ef75f0-0eb1-59c5-8ce1-bba0cd24c832
-- title:
--   Rigidifying an Atkin–Lehner quotient over the Frobenius-twisted leg
-- statement:
--   Fix a prime $r$ and a natural number $N$ with $r \nmid N$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $O^{\mathrm{nr}}$ with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, rationals $a,b$, and a $\mathbb Z$-submodule $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ containing every integer. Over $k_0 = O^{\mathrm{nr}}/(\pi)$ let $A_0$ and $A_0^{(r)}$ be fake elliptic curves of level $N$ with $\Lambda$-action, and $\mathrm{pr}_A : A_0^{(r)} \to A_0$ a morphism exhibiting $A_0^{(r)}$ as the pullback of $A_0$ along the map $k_0 \to k_0$ induced by $\mathrm{Fr}$ (`residueLeg`), i.e. a pullback square compatible with the relative group laws on points, with the $\Lambda$-actions, and with level structures. Further given morphisms $F : A_0 \to A_0^{(r)}$ and $V : A_0^{(r)} \to A_0$ over $k_0$ such that: both are additive on $T$-points for the relative group laws; $F$ intertwines $A_0.\mathrm{act}\,x$ with $A_0^{(r)}.\mathrm{act}\,x$ and $V$ conversely, for all $x \in \Lambda$; both carry points factoring through the level morphism `lev` to points factoring through `lev`; $V \circ F$ and $F \circ V$ are multiplication by $r$ on points (iterated group law, `nsmulPt`); and for every commutative ring $C$ of characteristic $r$ and every $x : \operatorname{Spec} C \to A_0$, one has $x$ followed by $F$ followed by $\mathrm{pr}_A$ equal to $x$ precomposed with $\operatorname{Spec}$ of the $r$-power Frobenius of $C$. The conclusion asserts: for every $\mathcal O$-algebra $B$, every $\mathcal O$-algebra map $\psi : O^{\mathrm{nr}} \to B$, every pair $E,E'$ of fake elliptic curves of level $N$ over $B$, and every pair of morphisms $q : E \to E'$, $q' : E' \to E$ over $B$ satisfying `IsAtkinLehnerQuotientVia r` (both additive on points, $\Lambda$-equivariant, $q \circ q'$ and $q' \circ q$ equal to the action of $r \in \Lambda$, the stated kernel criterion for $q$ on points, and preservation of level by $q$), and every rigidification $\rho$ of $E$ with respect to $\pi$, $A_0$ and $\psi$, there is a rigidification $\rho'$ of $E'$ with respect to the twisted leg $\psi \circ \mathrm{Fr}$ (`frobTwist Onr Fr 1 ψ`) together with: a morphism $q_b : \rho.E_b \to \rho'.E_b$ over $B/(\pi)$ with $q_b$ followed by $\rho'.g_b$ equal to $\rho.g_b$ followed by $q$; a morphism $u_A : \rho'.A_b \to A_0^{(r)}$ exhibiting $\rho'.A_b$ as the pullback of $A_0^{(r)}$ along `residueLeg π ψ`, with $u_A$ followed by $\mathrm{pr}_A$ equal to $\rho'.g_A$; a morphism $F_b : \rho.A_b \to \rho'.A_b$ over $B/(\pi)$ with $F_b$ followed by $u_A$ equal to $\rho.g_A$ followed by $F$; and natural numbers $i,j$ with $q_b$ followed by $\rho'.\varphi$ followed by $\rho'.A_b.\mathrm{act}\,[r^i]$ equal to $\rho.\varphi$ followed by $F_b$ followed by $\rho'.A_b.\mathrm{act}\,[r^j]$.
--
--   This is the transport of a rigidification (a reduction mod $\pi$ together with an isogeny of $r$-power degree to a base change of the fixed fake elliptic curve $A_0$ over the residue field) along an Atkin–Lehner quotient at $r$, the twist by one power of Frobenius in the structural leg $\psi$ being forced by the factorisation of the quotient through relative Frobenius. It feeds the construction of rigidifications in $\pi$-translate form used in the Čerednik–Drinfeld description of the curves, and uses the level-preservation of the dual Atkin–Lehner map, where $r \nmid N$ enters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_frobTwist_one_corr_relFrobenius_of_isAtkinLehnerQuotientVia_of_not_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_frobTwist_one_corr_relFrobenius_of_isAtkinLehnerQuotientVia_of_not_dvd
    {r N : ℕ} [Fact r.Prime]

    (hrN : ¬ r ∣ N)
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (prA : A₀r.A ⟶ A₀.A)
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
    (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f) (V : A₀r.A ⟶ A₀.A) (hV : V ≫ A₀.f = A₀r.f)
    (hFV : (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
        mapPt F hF (A₀.L.mul t P Q) = A₀r.L.mul t (mapPt F hF P) (mapPt F hF Q)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀r.f),
        mapPt V hV (A₀r.L.mul t P Q) = A₀.L.mul t (mapPt V hV P) (mapPt V hV Q)) ∧
      (∀ x : ↥Λ, A₀.act x ≫ F = F ≫ A₀r.act x) ∧ (∀ x : ↥Λ, A₀r.act x ≫ V = V ≫ A₀.act x) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
        FactorsThrough A₀.lev P → FactorsThrough A₀r.lev (mapPt F hF P)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
        FactorsThrough A₀r.lev Q → FactorsThrough A₀.lev (mapPt V hV Q)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
        mapPt V hV (mapPt F hF P) = nsmulPt A₀.L t r P) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
        mapPt F hF (mapPt V hV Q) = nsmulPt A₀r.L t r Q) ∧
      (∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀.A),
        x ≫ F ≫ prA = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x)) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
      (E E' : FakeEllipticCurve Λ N B)
      (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f),
      FakeEllipticCurve.IsAtkinLehnerQuotientVia r E E' q hq q' hq' →
      ∀ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E),
      ∃ ρ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr 1 ψ) E',
        (∃ (qb : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : qb ≫ ρ'.gb = ρ.gb ≫ q) (_ : qb ≫ ρ'.Eb.f = ρ.Eb.f)
          (uA : ρ'.Ab.A ⟶ A₀r.A)
          (_ : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρ'.Ab uA)
          (_ : uA ≫ prA = ρ'.gA)
          (Fb : ρ.Ab.A ⟶ ρ'.Ab.A) (_ : Fb ≫ uA = ρ.gA ≫ F) (_ : Fb ≫ ρ'.Ab.f = ρ.Ab.f)
          (i j : ℕ),
          qb ≫ ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ Fb ≫ ρ'.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by sorry
