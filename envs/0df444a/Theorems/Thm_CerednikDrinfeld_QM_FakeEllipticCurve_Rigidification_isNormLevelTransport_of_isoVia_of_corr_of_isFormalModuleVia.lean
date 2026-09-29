-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isNormLevelTransport_of_isoVia_of_corr_of_isFormalModuleVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isNormLevelTransport_of_isoVia_of_corr_of_isFormalModuleVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/ef9647b5-8fb0-53e2-91c8-18dcd154db2a
-- title:
--   Norm level transport is preserved by isomorphisms of rigidifications
-- statement:
--   Fix primes $r \neq \bar r$ and $N \geq 1$ with $r \nmid N$, and the standard Čerednik–Drinfel'd frame, whose hypotheses are summarised here in groups: a complete discrete valuation ring $\mathcal O$ of characteristic zero with irreducible $\pi$, residue ring of cardinality $r$ and $(r) = (\pi)$, with fraction field $K_0$; an $\mathcal O$-algebra $Onr$ that is $\pi$-adically complete, has maximal ideal $(\pi)$, is integral over $\mathcal O$ modulo $\pi$ and residually algebraically closed, equipped with $Fr$ satisfying $Fr(x) \equiv x^r \pmod \pi$; an indefinite quaternion algebra $\mathbb H[\mathbb Q, a, b]$ ramified exactly at $r$ and $\bar r$, a maximal order $\Lambda$ containing $\mathbb Z$ and an order coordinate $\mathrm{coord} : \Lambda \to \mathbb{Z}_{r^2}^{\,2}$; a fake elliptic curve $A_0$ over $Onr/\pi$ with a formal $\mathcal O_D$-module structure $(X_0, \theta_0)$ via $\mathrm{coord}$, $X_0$ of height $4$; $\iota : \mathbb{Z}_{r^2} \to Onr$, a special formal $\mathcal O_D$-module $\Phi$ of height $4$ over $Onr/(r)$, a moduli package $M$ that is a Zariski sheaf together with $\eta$ identifying admissible rigidified objects up to isomorphism, naturally and locally surjectively; an injective map $E_0$ of the centraliser of the $\mathbb{Z}_{r^2}$-action and $\varpi$ on $\Phi$ into $M_2(K_0)$, commensurable with $M_2(\mathcal O)$ after scaling by a power of $r$; a reduction map $\kappa$ compatible with the quotient maps and an isogeny $\beta_0$ of height $4n_0$ from $\Phi$ to $X_0$ pushed along $\kappa$; and a full level-$n$ structure $P_0$ on $A_0$ with $r \nmid n$. Let $B$ be a Noetherian $\mathcal O$-algebra in which $\pi$ is nilpotent, $\psi : Onr \to B$ an $\mathcal O$-algebra map, and let $E, E'$ be fake elliptic curves of level $N$ for $\Lambda$ over $B$ together with an isomorphism $i$ of their total spaces over $B$ that respects the group law, the $\Lambda$-action and the level subscheme. Let $\varrho, \varrho'$ be rigidifications of $E, E'$ relative to $\psi$ and $A_0$, and suppose they correspond along $i$ up to powers of $r$: there are $ib : \varrho.E_b \to \varrho'.E_b$ over $B/\pi$ with $ib$ followed by $\varrho'.g_b$ equal to $\varrho.g_b$ followed by $i$, and $u_A : \varrho'.A_b \to \varrho.A_b$ exhibiting $\varrho'.A_b$ as the pullback of $\varrho.A_b$ along the identity with $u_A$ followed by $\varrho.g_A$ equal to $\varrho'.g_A$, and naturals $i_1, j_1$ with $ib \cdot \varrho'.\varphi \cdot u_A \cdot [r^{i_1}] = \varrho.\varphi \cdot [r^{j_1}]$ as maps $\varrho.E_b \to \varrho.A_b$. Finally let $P_n$, $P'_n$ be full level-$n$ structures on $E$, $E'$ whose sections satisfy $i \circ P_n = P'_n$. The assertion is that if $P_n$ is a normalised level transport of $P_0$ along $\varrho$ — that is, there is a section $Q$ of $\varrho.A_b$ over $B/\pi$ reducing $P_0$ along the residue leg of $\psi$, a formal $\mathcal O_D$-module structure $(X, \theta)$ on $E$ via $\mathrm{coord}$, an index $j \leq 1$ and a rigidified object $t$ over $B$ with $t.X = X$ which is a rigidified transport of $(\theta_0, \kappa, \beta_0)$ along $\varrho$ in parity $j$, is admissible for $\iota$ and the $(-j)$-th Frobenius twist of $\psi$, and satisfies that the reduction modulo $\pi$ of $r^{t.n} \cdot P_n$ equals $Q$ followed by $\varrho.\varphi'$ and $\varrho.g_b$ — then the same holds for $P'_n$ with respect to $\varrho'$.
--
--   This is the invariance of the height-normalised level transport condition of the Čerednik–Drinfel'd comparison under an isomorphism of fake elliptic curves whose rigidifications correspond up to $r$-power multiples, the bookkeeping being possible because the level $n$ is prime to $r$. It is used in the local constructions of full level structures on the Drinfel'd side, for instance in the statements producing such structures locally on a connected base and in the transfer of rigidifications along pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isNormLevelTransport_of_isoVia_of_corr_of_isFormalModuleVia.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isNormLevelTransport_of_isoVia_of_corr_of_isFormalModuleVia
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
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    {n : ℕ} (P₀ : A₀.FullLevel n) (hrn : ¬ r ∣ n)
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))

    (E E' : FakeEllipticCurve Λ N B) (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hiso : FakeEllipticCurve.IsoVia E E' i hi)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hibg : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (Pn : E.FullLevel n) (Pn' : E'.FullLevel n) (hPn : mapPt i.hom hi Pn.P = Pn'.P)
    (h : FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn) :
    FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ' Pn' := by sorry
