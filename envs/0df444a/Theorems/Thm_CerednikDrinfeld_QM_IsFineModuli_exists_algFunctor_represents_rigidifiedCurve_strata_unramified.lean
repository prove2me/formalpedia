-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_algFunctor_represents_rigidifiedCurve_strata_unramified
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/b2b5b0a3-c92c-5e9b-8250-6c6deca806bc
-- title:
--   Rigidified-pair functor over the fine moduli scheme, with unramified strata
-- statement:
--   Throughout, the data are those of the Čerednik–Drinfeld situation at a prime $r$. Fixed are: a prime $r$ and a nonzero natural number $N$ with $r \nmid N$; a prime $\bar r \neq r$; a commutative ring $\mathcal O$ and an element $\pi \in \mathcal O$ with $(r) = (\pi)$ as ideals of $\mathcal O$ (the hypothesis `hunr`); an $\mathcal O$-algebra $Onr$; rationals $a, b$ such that `IsIndefiniteRamifiedExactlyAt a b r rbar` holds, i.e. $0 < a$ or $0 < b$, and a finite place $v$ of $\mathbb Q$ has the property that every nonzero element of $\mathbb H[\mathbb Q, a, b] \otimes_{\mathbb Q} \mathbb Q_v$ is a unit precisely when $v$ lies over $r$ or over $\bar r$; a $\mathbb Z$-submodule $\Lambda \subseteq \mathbb H[\mathbb Q, a, b]$ which is a maximal order (an order — containing $1$, closed under multiplication, spanning the algebra over $\mathbb Q$, finitely generated — maximal among orders containing it) and contains every rational integer (`hΛℤ`); an element $\mu_\Lambda \in \Lambda$ with $\mu_\Lambda^2 = -(r\bar r) \cdot 1$ and a map $\mathrm{star}_\Lambda : \Lambda \to \Lambda$ with $\mu_\Lambda \cdot \mathrm{star}_\Lambda(x) = \bar x \cdot \mu_\Lambda$ for all $x \in \Lambda$; the assumption that $2$ is a unit in $\mathcal O$; a map $\mathrm{coord} : \Lambda \to \mathbb W(\mathbb F_{r^2})^2$ satisfying `IsOrderCoord`, that is, additive, sending $1$ to $(1,0)$, multiplicative for the twisted law with Frobenius and the factor $r$, injective, with $r$-adically dense image in each coordinate, and compatible with reduced traces; a fake elliptic curve $A_0$ over $Onr/\pi\,Onr$ with $\Lambda$-action and level-$N$ data; a natural number $n \geq 3$ with $r \nmid n$; a scheme $M$ with a morphism $f_M : M \to \operatorname{Spec} \mathcal O$ and a family of points $\mathrm{ptF}$ assigning to each ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec} \mathcal O$ and each pair $u$ consisting of a fake elliptic curve over $S$ with $\Lambda$-action, level $N$ and a full level-$n$ structure, a morphism $\operatorname{Spec} S \to M$ over $s$, such that `IsFineModuli` holds: $\mathrm{ptF}$ is constant on isomorphism classes, compatible with pullback of such data along ring maps, surjective on $s$-points of $f_M$, and separates non-isomorphic data.
--
--   The base of the construction is a Noetherian $\mathcal O$-algebra $C$ in which the image of $\pi$ is nilpotent (`hC`), together with an $\mathcal O$-algebra map $\psi : Onr \to C$ (the coefficient leg).
--
--   The conclusion asserts the existence of: a functor $PR$ from $C$-algebras to types (a [`CerednikDrinfeld.FormalOmega.AlgFunctor C`](def/CerednikDrinfeld_FormalUpperHalfPlaneCharts.html#L10), with its object assignment, its action on $C$-algebra maps and the identity and composition laws); an assignment $\mathrm{ptR}$ which, for every $C$-algebra $S$ that is also an $\mathcal O$-algebra compatibly with $C$, every $\mathcal O$-algebra map $\psi_S : Onr \to S$ that equals $\psi$ followed by $C \to S$, every $u$ as above over $S$ and every rigidification $\rho$ of $u.1$ relative to $(r, \pi, A_0, \psi_S)$, produces an element of $PR(S)$; and an assignment $\mathrm{toM}$ sending an element of $PR(S)$ to a morphism $\operatorname{Spec} S \to M \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec} C$ whose composite with the second projection is $\operatorname{Spec}$ of $C \to S$. (A rigidification consists of a fake elliptic curve $E_b$ over $S/\pi S$ together with $g_b$ exhibiting $E_b$ as the pullback of $u.1$ along $S \to S/\pi S$, a fake elliptic curve $A_b$ over $S/\pi S$ with $g_A$ exhibiting $A_b$ as the pullback of $A_0$ along the map induced by $\psi_S$, a natural number $d$, and mutually inverse up to $r^d$ morphisms $\varphi : E_b \to A_b$, $\varphi'$, forming an $r^d$-isogeny pair and preserving the level data.)
--
--   These satisfy the following ten conjuncts.
--
--   (1) Sheaf property for Zariski coverings by distinguished opens: for every $C$-algebra $A$, every natural number (the binder reuses the name $n$, shadowing the level) and every $f : \mathrm{Fin}\,n \to A$ whose range generates the unit ideal, every family $B_i$ of $A$-algebras which are also $C$-algebras compatibly and are localisations of $A$ away from $f_i$, and every family of sections $s_i \in PR(B_i)$: if for all $i, j$, every $C$- and $A$-algebra $D$ which is a localisation away from $f_i f_j$ and all $A$-algebra maps $\rho_1 : B_i \to D$, $\rho_2 : B_j \to D$ the images of $s_i$ and $s_j$ in $PR(D)$ agree, then there is a unique $s_0 \in PR(A)$ whose image in each $PR(B_i)$ is $s_i$.
--
--   (2) Naturality of $\mathrm{toM}$: for $C$-algebras $S, S'$, a $C$-algebra map $\varphi$ and $x \in PR(S)$, the morphism underlying $\mathrm{toM}(PR(\varphi)(x))$ is $\operatorname{Spec}\varphi$ followed by the morphism underlying $\mathrm{toM}(x)$.
--
--   (3) Invariance of $\mathrm{ptR}$ under isomorphism of rigidified pairs over a fixed $S$: given $u, u'$ over $S$ with rigidifications $\rho, \rho'$, an isomorphism $i : u.1.A \cong u'.1.A$ with $i \circ u'.1.f = u.1.f$ compatible with the group laws, the $\Lambda$-actions, the level subschemes in both directions and carrying the full level-$n$ point of $u$ to that of $u'$ (`WithFullLevel.IsoVia`), and, in addition, morphisms $i_b : \rho.E_b.A \to \rho'.E_b.A$ with $i_b$ followed by $\rho'.g_b$ equal to $\rho.g_b$ followed by $i$ and $i_b$ compatible with the structure morphisms, $u_A : \rho'.A_b.A \to \rho.A_b.A$ exhibiting $\rho'.A_b$ as the pullback of $\rho.A_b$ along the identity and satisfying $u_A$ followed by $\rho.g_A$ equal to $\rho'.g_A$, and natural numbers $i_1, j_1$ with $i_b$ followed by $\rho'.\varphi$, then $u_A$, then the action of $r^{i_1}$ equal to $\rho.\varphi$ followed by the action of $r^{j_1}$ — then the two points of $PR(S)$ coincide.
--
--   (4) Compatibility of $\mathrm{ptR}$ with base change: for $S, S'$ both $C$- and $\mathcal O$-algebras compatibly, a $C$-algebra map $\varphi : S \to S'$, $\psi_S$ as above with the two compatibility hypotheses $h\psi_S$ and $h\psi_{S'}$, data $u$ over $S$ and $u'$ over $S'$ with rigidifications $\rho$ and $\rho'$ (the latter relative to $\varphi \circ \psi_S$), and $g : u'.1.A \to u.1.A$ exhibiting $u'.1$ as the pullback of $u.1$ along $\varphi$ (pullback square, compatibility with the group law, with the $\Lambda$-action and with level factorisation) and carrying the full level-$n$ point correctly, if $\rho'$ is the pullback of $\rho$ along $(\varphi, g)$ in the sense of `Rigidification.IsPullbackVia`, then $PR(\varphi)$ applied to the point of $(u, \rho)$ is the point of $(u', \rho')$.
--
--   (5) Surjectivity: for every $S$, $\psi_S$ as above and every $z \in PR(S)$ there are $u$ and a rigidification $\rho$ of $u.1$ with $\mathrm{ptR}(u, \rho) = z$.
--
--   (6) Injectivity over connected base: if moreover every idempotent of $S$ is $0$ or $1$, and $(u, \rho)$, $(u', \rho')$ have the same point of $PR(S)$, then there exist $i$ and the verification that it is an isomorphism of curves-with-level as in (3), together with $i_b$, $u_A$ and natural numbers $i_1, j_1$ satisfying exactly the relations listed in (3).
--
--   (7) $\mathrm{toM}$ forgets the rigidification: the morphism underlying $\mathrm{toM}(\mathrm{ptR}(u,\rho))$ followed by the first projection of the fibre product equals the morphism underlying $\mathrm{ptF}$ applied to $u$ over $\operatorname{Spec}$ of $\mathcal O \to S$.
--
--   (8) Unique lifting along square-zero surjections: for a Noetherian $C$-algebra $S$, a $C$-algebra $S_0$ and a surjective $C$-algebra map $p : S \to S_0$ whose kernel has square zero, for every $x_0 \in PR(S_0)$ and every $\operatorname{Spec} S$-point $t$ of $M \times_{\operatorname{Spec}\mathcal O}\operatorname{Spec} C$ over $\operatorname{Spec} C$ whose restriction along $\operatorname{Spec} p$ is the morphism underlying $\mathrm{toM}(x_0)$, there is a unique $x \in PR(S)$ with $PR(p)(x) = x_0$ and $\mathrm{toM}(x) = t$.
--
--   (9) Reduction modulo $\pi$: for a Noetherian $C$-algebra $T$, writing $\bar T = T/(\pi)$ for the quotient by the ideal generated by the image of $\pi$, for every $\bar x \in PR(\bar T)$ and every $\operatorname{Spec} T$-point $t$ of the fibre product over $\operatorname{Spec} C$ whose restriction to $\operatorname{Spec}\bar T$ is the morphism underlying $\mathrm{toM}(\bar x)$, there is a unique $x \in PR(T)$ with $PR(\text{quotient map})(x) = \bar x$ and $\mathrm{toM}(x) = t$.
--
--   (10) Degree strata: there exist schemes $X_d$ for $d \in \mathbb N$, morphisms $\xi_d : X_d \to M \times_{\operatorname{Spec}\mathcal O}\operatorname{Spec} C$, each locally of finite presentation and formally unramified, and an assignment $\mathrm{pt}$ sending a $T$-point $x$ of $X_d$ over $\operatorname{Spec} C$ (a morphism $\operatorname{Spec} T \to X_d$ over the structure map, $T$ a $C$-algebra) to an element $\mathrm{pt}(d,T,x) \in PR(T)$, such that: (a) the existence of such a $T$-point forces the image of $\pi$ in $T$ to be $0$; (b) the morphism underlying $\mathrm{toM}(\mathrm{pt}(d,T,x))$ is $x$ followed by $\xi_d$; (c) $\mathrm{pt}$ is natural, i.e. if $x' = \operatorname{Spec}\varphi$ followed by $x$ for a $C$-algebra map $\varphi : T \to T'$, then $\mathrm{pt}(d,T',x') = PR(\varphi)(\mathrm{pt}(d,T,x))$; (d) there is an assignment $\mathrm{ptX}$ producing, for every $d$, every $T$ which is a $C$- and $\mathcal O$-algebra compatibly, every $\psi_T$ as above, every $u$ over $T$ and every rigidification $\rho$ of $u.1$ with $\rho.d = d$ and with $\pi$ mapping to $0$ in $T$, a $T$-point of $X_d$ over $\operatorname{Spec} C$, subject to four conditions: $\mathrm{pt}(d,T,\mathrm{ptX}(\dots)) = \mathrm{ptR}(u,\rho)$; $\mathrm{ptX}$ is compatible with base change along a $C$-algebra map $\varphi : T \to T'$ given pullback data $(g, hg)$ for $u, u'$, the compatibility of the full level-$n$ points, and $\rho'$ the pullback of $\rho$, both of degree $d$ and with $\pi$ zero in $T$ and $T'$, in the sense that the morphism for $(u',\rho')$ is $\operatorname{Spec}\varphi$ followed by that for $(u,\rho)$; every $T$-point of $X_d$ over $\operatorname{Spec} C$ is of the form $\mathrm{ptX}(d,T,\psi_T,u,\rho)$ for some $u$, $\rho$ with $\rho.d = d$; and two such points $\mathrm{ptX}(d,T,\psi_T,u,\rho)$ and $\mathrm{ptX}(d,T,\psi_T,u',\rho')$ are equal if and only if there is an isomorphism $i$ of curves-with-full-level as in (3), together with $i_b$ and $u_A$ satisfying the same compatibilities as in (3) but now with the untwisted relation: $i_b$ followed by $\rho'.\varphi$ and then $u_A$ equals $\rho.\varphi$; and (e) for every $d$, $T$, $\psi_T$, $u$ and $\rho$ with $\pi$ zero in $T$, the point $\mathrm{ptR}(u,\rho)$ lies in the image of $\mathrm{pt}(d,T,\cdot)$ if and only if $u.1$ carries a rigidification $\rho'$ with $\rho'.d = d$ and $\mathrm{ptR}(u,\rho') = \mathrm{ptR}(u,\rho)$.
--
--   This is the relative moduli statement for rigidified pairs in the Čerednik–Drinfeld uniformisation of a Shimura curve at the prime $r$: over a Noetherian base $C$ in which $\pi$ is nilpotent, the pairs (fake elliptic curve with full level $n$, rigidification of its reduction by an $r^d$-isogeny to the fixed curve $A_0$) are organised into a functor on $C$-algebras which is a Zariski sheaf, has unique lifting along square-zero surjections and along reduction modulo $\pi$, and is exhausted by degree strata that are locally of finite presentation and formally unramified over $M_C$. It is used in the construction and uniqueness of even rigidified pairs, where $2$ being invertible enters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_algFunctor_represents_rigidifiedCurve_strata_unramified.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (μΛ : ↥Λ) (hμΛ : (μΛ : ℍ[ℚ, a, b]) * (μΛ : ℍ[ℚ, a, b]) = -(((r * rbar : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (starΛ : ↥Λ → ↥Λ) (hstarΛ : ∀ x : ↥Λ, (μΛ : ℍ[ℚ, a, b]) * (starΛ x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μΛ)
    (h2 : IsUnit ((2 : ℕ) : 𝒪))

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C) :
    ∃ (PR : CerednikDrinfeld.FormalOmega.AlgFunctor C)

      (ptR : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (ψS : Onr →ₐ[𝒪] S) (_ : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S), FakeEllipticCurve.Rigidification r π A₀ ψS u.1 → PR.obj S)
      (toM : ∀ (S : Type) [CommRing S] [Algebra C S],
        PR.obj S → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),

      (∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A),
        Ideal.span (Set.range f) = ⊤ →
        ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
          [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, PR.obj (B i)),
        (∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
            [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
            PR.map (ρ₁.restrictScalars C) (s i) = PR.map (ρ₂.restrictScalars C) (s j)) →
        ∃! s₀ : PR.obj A, ∀ i, PR.map (IsScalarTower.toAlgHom C A (B i)) s₀ = s i) ∧

      (∀ (S S' : Type) [CommRing S] [Algebra C S] [CommRing S'] [Algebra C S'] (φ : S →ₐ[C] S') (x : PR.obj S),
          (toM S' (PR.map φ x)).1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (toM S x).1) ∧

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1)
          (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f),
          FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi →
          (∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ') ∧

      (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
          (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
          (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
          (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
          FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
            PR.map φ (ptR S ψS hψS u ρ) = ptR S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ') ∧

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ) (z : PR.obj S),
          ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1), ptR S ψS hψS u ρ = z) ∧
      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
          (hSc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1),
          ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ' →
            ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
              ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
          (toM S (ptR S ψS hψS u ρ)).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
            (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1) ∧

      (∀ (S S₀ : Type) [CommRing S] [IsNoetherianRing S] [Algebra C S] [CommRing S₀] [Algebra C S₀] (p : S →ₐ[C] S₀),
          Function.Surjective p → RingHom.ker (p : S →+* S₀) ^ 2 = ⊥ →
          ∀ (x₀ : PR.obj S₀) (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
          Spec.map (CommRingCat.ofHom (p : S →+* S₀)) ≫ t.1 = (toM S₀ x₀).1 →
          ∃! x : PR.obj S, PR.map p x = x₀ ∧ toM S x = t) ∧

      (∀ (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra C T]
          (xb : PR.obj (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))
          (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ t.1 =
            (toM _ xb).1 →
          ∃! x : PR.obj T,
            PR.map (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) x = xb ∧ toM T x = t) ∧

      (∃ (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
          (_ : ∀ d, LocallyOfFinitePresentation (ξ d)) (_ : ∀ d, FormallyUnramified (ξ d))
          (pt : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T],
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) → PR.obj T),

          (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
              (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
              algebraMap C T (algebraMap 𝒪 C π) = 0) ∧

          (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
              (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
              (toM T (pt d T x)).1 = x.1 ≫ ξ d) ∧

          (∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T')
              (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
              (x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T'))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
              x'.1 = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ x.1 → pt d T' x' = PR.map φ (pt d T x)) ∧

          (∃ (ptX : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
              (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
              ρ.d = d → algebraMap C T (algebraMap 𝒪 C π) = 0 → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),

            (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
                (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
                pt d T (ptX d T ψT hψT u ρ hd h0) = ptR T ψT hψT u ρ) ∧

            (∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
                (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
                (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
                (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
                (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
                (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
                FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                  (ptX d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                    Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (ptX d T ψT hψT u ρ hd h0).1) ∧

            (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  ptX d T ψT hψT u ρ hd h0 = x) ∧

            (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                (ptX d T ψT hψT u ρ hd h0 = ptX d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ))) ∧

          (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
              (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
              algebraMap C T (algebraMap 𝒪 C π) = 0 →
              ((∃ x, pt d T x = ptR T ψT hψT u ρ) ↔
                ∃ (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u.1), ρ'.d = d ∧ ptR T ψT hψT u ρ' = ptR T ψT hψT u ρ))) := by sorry
