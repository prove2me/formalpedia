-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidifiedToG_natural_isRigTransport
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedToG_natural_isRigTransport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/0699792e-57b5-547c-85ba-8d8c900a6961
-- title:
--   Forgetful map from rigidified fake elliptic curves to G-points
-- statement:
--   Fix primes $r,\bar r$ with $\bar r\neq r$ and a nonzero level $N$ with $r\nmid N$. The arithmetic frame consists of: a characteristic-zero discrete valuation domain $\mathcal O$ with irreducible element $\pi$, $\pi$-adically complete, with $\#(\mathcal O/\pi)=r$ and $(r)=(\pi)$, a fraction field $K_0$ of $\mathcal O$; and a characteristic-zero $\mathcal O$-domain $Onr$ with an $\mathcal O$-algebra automorphism $Fr$, complete for the ideal $(\pi)$, with $(\pi)$ maximal in $Onr$, every element of $Onr$ satisfying a monic $\mathcal O$-polynomial modulo $\pi$, every monic polynomial of positive degree over $Onr$ having a root modulo $\pi$, and $Fr\,x\equiv x^r \pmod\pi$. The quaternionic data: rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and, place by place, is a division algebra over the completion exactly at the places above $r$ and $\bar r$; a maximal order $\Lambda$ containing all integers; a map $\mathrm{coord}:\Lambda\to \mathbb Z_{r^2}\times\mathbb Z_{r^2}$ satisfying `IsOrderCoord` (additive, $1\mapsto(1,0)$, the Frobenius-twisted multiplication rule, injective, dense, and the trace compatibility); a fake elliptic curve $A_0$ over $Onr/\pi$ together with a formal $\mathcal O_D$-module $X_0$ of height $4$ and formal coordinates $\theta_0$ exhibiting $A_0$ as a formal module via $\mathrm{coord}$. Drinfeld's datum: a ring map $\iota:\mathbb Z_{r^2}\to Onr$, a special formal $\mathcal O_D$-module $\Phi$ of height $4$ over $Onr/(r)$ relative to $\iota$ reduced, a moduli package $M$ over $Onr$ which is a Zariski sheaf, a family of maps $\eta$ from rigidified objects $\mathrm{Rig}(r,\Phi,B)$ to $M(B)$ for every $Onr$-algebra $B$ with $r$ nilpotent, subject to three laws (on Noetherian $B$: $\eta$ identifies two admissible rigidified objects precisely when they are isomorphic; $\eta$ commutes with base change along ring maps over $Onr$; every point of $M(B)$ becomes, on the members of a finite cover of $B$ by localisations, the image under $\eta$ of an admissible rigidified object), and an injective ring map $E_0$ from the centraliser of the $\mathbb Z_{r^2}$-action and of $\varpi$ on $\Phi$ into $M_2(K_0)$ whose image is commensurable with $M_2(\mathcal O)$ in the sense that for some $m$ it contains $r^m M_2(\mathcal O)$ and is contained in $r^{-m}M_2(\mathcal O)$. Finally a ring map $\kappa:Onr/\pi\to Onr/(r)$ compatible with the two quotient maps, and a series $\beta_0$ which is an $\mathcal O_D$-isogeny $\Phi\to X_0\otimes_\kappa$ of height $4n_0$. The conclusion asserts the existence of a family $\Xi$ which, for every Noetherian $\mathcal O$-algebra $B$ in which $\pi$ is nilpotent, every $\mathcal O$-algebra map $\psi:Onr\to B$ and every rigidified curve $x=(E,\rho)$ over $(B,\psi)$, produces a $G$-point of $M$ over $B$, i.e. a triple consisting of a leg $Onr\to B$, nilpotence of $r$, and a point of $M$, such that: (i) if $B$ has no idempotents other than $0$ and $1$, the leg of $\Xi B\,\psi\,x$ is $\psi\circ Fr^{k}$ for some $k\in\mathbb Z$; (ii) $\Xi$ is compatible with pullback, in that for $\varphi:B\to B'$ over $\mathcal O$ and rigidified curves $x$ over $(B,\psi)$, $x'$ over $(B',\varphi\circ\psi)$ whose underlying curves are related by a $\Lambda$-equivariant pullback square $g$ and whose rigidifications correspond under $\varphi$ and $g$, one has $\Xi B'\,(\varphi\circ\psi)\,x'=(\Xi B\,\psi\,x)$ base-changed along $\varphi$; (iii) $\Xi$ is invariant under isomorphism: if $i$ is an isomorphism of the underlying curves of $x,x'$ over $B$ compatible with the group law, the $\Lambda$-action and the level structure, and if the two rigidifications are linked by maps $ib$ on the reductions and $uA$ on the $A_0$-pullbacks compatible with $gb$, $gA$ and the structure morphisms and satisfying $ib\circ x'.\varphi\circ uA\circ[r^{i_1}]=x.\varphi\circ[r^{j_1}]$ for some exponents $i_1,j_1$, then $\Xi B\,\psi\,x=\Xi B\,\psi\,x'$; and (iv) the defining clause: if moreover $B$ has no nontrivial idempotents, $r$ is nilpotent in $B$, and $(X,\theta)$ exhibits the underlying curve of $x$ as a formal module via $\mathrm{coord}$, then there are $j\le 1$ and a rigidified object $t$ over $B$ with $t.X=X$, with $t$ obtained from $\theta_0$, $\kappa$, $\beta_0$, the rigidification of $x$ and $\theta$ by rig-transport with Frobenius exponent $j$, with $t$ admissible for $\iota$ and the twisted leg $\psi\circ Fr^{-j}$, and with $\Xi B\,\psi\,x$ equal to the $G$-point whose leg is $\psi\circ Fr^{-j}$ and whose point is $\eta B\,(\psi\circ Fr^{-j})\,t$.
--
--   This is the forgetful direction of the supersingular dictionary underlying the Čerednik–Drinfeld uniformisation: it attaches to a fake elliptic curve rigidified along its reduction a point of Drinfeld's moduli functor of special formal $\mathcal O_D$-modules, canonically up to the Frobenius twist of the unramified leg and up to an $r$-power ambiguity in the isogeny. It is used in the construction of the $p$-adic uniformisation of Shimura curves with fine level structure and of the associated Atkin–Lehner data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidifiedToG_natural_isRigTransport.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedToG_natural_isRigTransport
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hX₀ : X₀.HasHeight 4)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r Onr) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀)) :
    ∃ Ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
        IsNilpotent (algebraMap 𝒪 B π) → FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ → ModuliPackage.GPoint 𝒪 M B,

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ), ∃ k : ℤ, (Ξ B ψ hB x).ψ = frobTwist Onr Fr k ψ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B' (φ.comp ψ))
          (g : x'.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') x.1 x'.1 g),
          FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg x.2 x'.2 → Ξ B' (φ.comp ψ) hB' x' = (Ξ B ψ hB x).map φ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f),
          FakeEllipticCurve.IsoVia x.1 x'.1 i hi →
          (∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
            (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
            (i₁ j₁ : ℕ),
            ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            Ξ B ψ hB x = Ξ B ψ hB x') ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hBr : IsNilpotent ((r : ℕ) : B))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2),
          x.1.IsFormalModuleVia coord X θ →
          ∃ (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
            FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t ∧
            t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
            Ξ B ψ hB x = ⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hBr, η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t⟩) := by sorry
