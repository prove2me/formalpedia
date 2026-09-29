-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_PR_existsUnique_map_eq_of_span_eq_top
-- name    : CerednikDrinfeld.QM.RigidifiedPairClass.PR.existsUnique_map_eq_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/cd76ad3b-ebba-5ce0-9b34-e2d1486062f0
-- title:
--   Zariski gluing for the rigidified pair class functor PR
-- statement:
--   The setting is the following. A prime $r$ and a nonzero natural number $N$ with $r \nmid N$ are fixed, together with a prime $\bar r \ne r$. A commutative ring $\mathcal O$ with an element $\pi$ is given such that $\mathrm{span}\{r\} = \mathrm{span}\{\pi\}$ in $\mathcal O$ (hypothesis `hunr`), together with an $\mathcal O$-algebra $O_{nr}$. Rationals $a, b$ are given with `hBq`: the quaternion algebra $\mathbb H[\mathbb Q, a, b]$ satisfies $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completed algebra $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ is a division algebra precisely when $r \in v$ or $\bar r \in v$. A $\mathbb Z$-submodule $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ is assumed to be a maximal order (`hΛ`: $\Lambda$ contains $1$, is closed under multiplication, spans the algebra over $\mathbb Q$, is finitely generated, and is maximal among such) and to contain all rational integers (`hΛℤ`). A map $\mathrm{coord} : \Lambda \to \mathbb W(\mathbb F_{r^2})^2$ is given which is an order coordinate in the sense of `IsOrderCoord` (`hcoord`: additive, sending $1$ to $(1,0)$, multiplicative in the twisted sense involving the Frobenius of Witt vectors, injective, with dense image in the $r$-adic sense, and compatible with reduced traces). Finally $A_0$ is a fake elliptic curve with $\Lambda$-action and level-$N$ structure over $O_{nr}/(\pi)$.
--
--   A level $n \ge 3$ with $r \nmid n$ is fixed, together with a scheme $M$, a morphism $f_M : M \to \operatorname{Spec} \mathcal O$ and a point rule $\mathrm{ptF}$ assigning to every commutative ring $S$, every morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and every fake elliptic curve with full level-$n$ structure over $S$ a section of $f_M$ over $s$; the hypothesis `hM` asserts that this makes $(M, f_M, \mathrm{ptF})$ a fine moduli scheme, i.e. $\mathrm{ptF}$ is invariant under isomorphism of level structures, compatible with pullback along ring maps, surjective on $s$-points of $f_M$, and injective up to isomorphism.
--
--   The base of the deformation side is a Noetherian commutative $\mathcal O$-algebra $C$ in which the image of $\pi$ is nilpotent (`hC`), with a chosen $\mathcal O$-algebra map $\psi : O_{nr} \to C$. Write $M_C$ for the fibre product of $f_M$ along $\operatorname{Spec} C \to \operatorname{Spec}\mathcal O$. Stratum schemes $X_d$, $d \in \mathbb N$, are given with structure morphisms $\xi_d : X_d \to M_C$; a rule $t_M$ assigns to every $C$-algebra $T$ and every fake elliptic curve with full level-$n$ structure over $T$ a point of $M_C$ over $\operatorname{Spec} T \to \operatorname{Spec} C$; and a rule $\mathrm{xOf}$ assigns to every $C$- and $\mathcal O$-algebra $T$ in a scalar tower over $C$, every $\mathcal O$-algebra map $\psi_T : O_{nr} \to T$ factoring as $\psi$ followed by $C \to T$, every curve with full level structure $u$ over $T$ and every rigidification $\rho$ of $u_1$ in the sense of `FakeEllipticCurve.Rigidification` (a reduction $E_b$ of the curve modulo $\pi$ together with a pullback datum, a reduction $A_b$ of $A_0$ along the induced map of quotients, an integer $d$, and a pair of mutually inverse $r^d$-isogenies $\varphi, \varphi'$ between $E_b$ and $A_b$ preserving the level structure), a morphism $\operatorname{Spec}(T/(\pi)) \to X_{\rho.d}$ whose composite with $\xi_{\rho.d}$ equals the reduction map followed by $t_M(T, u)$.
--
--   Four compatibility hypotheses are imposed on the derived point rule $\mathrm{ptX}$ built from $\mathrm{xOf}$ (the rule sending such data, with $\rho.d = d$ and $\pi = 0$ in $T$, to a point of $X_d$ over $\operatorname{Spec} T$). The hypothesis `hx2` is naturality: for a $C$-algebra map $\varphi : T \to T'$, compatible $\psi_T$, curves $u$ over $T$ and $u'$ over $T'$ related by a pullback morphism $g$ compatible with the level sections, and rigidifications $\rho, \rho'$ of the same degree $d$ related by `Rigidification.IsPullbackVia` along $\varphi$ and $g$, the point $\mathrm{ptX}$ of $(u', \rho')$ is $\operatorname{Spec}\varphi$ followed by the point $\mathrm{ptX}$ of $(u, \rho)$. The hypothesis `hx3` is surjectivity: every point of $X_d$ over $\operatorname{Spec} T$ (with $\pi = 0$ in $T$) arises as $\mathrm{ptX}$ of some pair $(u, \rho)$ with $\rho.d = d$. The hypothesis `hx4` is injectivity up to isomorphism: two such pairs over the same $T$ give the same $\mathrm{ptX}$ point if and only if there is an isomorphism $i$ of the underlying curves over $T$ compatible with the group laws, the $\Lambda$-action, the level subschemes and the level section (`WithFullLevel.IsoVia`), together with morphisms $i_b : \rho.E_b \to \rho'.E_b$ over the reductions and $u_A : \rho'.A_b \to \rho.A_b$ realising $\rho'.A_b$ as a pullback of $\rho.A_b$ along the identity, compatible with $\rho.g_b, \rho'.g_b$, with the structure morphisms and with $\rho.g_A, \rho'.g_A$, and satisfying $i_b$ followed by $\rho'.\varphi$ followed by $u_A$ equal to $\rho.\varphi$. The hypothesis `hxM` fixes the $M$-coordinate: the $\mathrm{ptX}$ point of $(u, \rho)$, followed by $\xi_d$ and by the first projection of $M_C$, equals $\mathrm{ptF}(T, u)$. Finally `hmap` is `MapCompat`: the local relation `Rel` on presented points is preserved by base change, i.e. for every $C$-algebra map $\varphi : T \to T'$ and presented points $p, q$ over $T$, if $p$ and $q$ are `Rel`-related then so are their images under `Pt.map` $\varphi$.
--
--   Under these hypotheses, let $\mathrm{PR}$ denote the `AlgFunctor` over $C$ attached to this data (the functor of presented points modulo the relation `Rel`). The conclusion is: for every commutative $C$-algebra $A$, every $m \in \mathbb N$ and every family $f : \mathrm{Fin}\, m \to A$ whose range generates the unit ideal of $A$, for every family of commutative $C$-algebras $B_i$ which are also $A$-algebras in a scalar tower over $C$ and which realise the localisation of $A$ away from $f_i$, and for every family of sections $s_i \in \mathrm{PR}(B_i)$ satisfying the cocycle condition — for all $i, j$ and every $A$-algebra $D$ which is also a $C$-algebra in a scalar tower and realises the localisation of $A$ away from $f_i f_j$, and for all $A$-algebra maps $\rho_1 : B_i \to D$ and $\rho_2 : B_j \to D$, the images $\mathrm{PR}(\rho_1)(s_i)$ and $\mathrm{PR}(\rho_2)(s_j)$ coincide — there exists a unique $s_0 \in \mathrm{PR}(A)$ such that for every $i$ the image of $s_0$ under the structure map $A \to B_i$ equals $s_i$.
--
--   This is the sheaf condition for the Zariski topology on $C$-algebras for the functor $\mathrm{PR}$ of rigidified fake elliptic curves with level structure lying in the $r$-power-isogeny strata $X_d$ over $M_C$, in the Čerednik–Drinfeld comparison for Shimura curves attached to an indefinite quaternion algebra ramified exactly at $r$ and $\bar r$. It is the gluing clause used by [`CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified), which asserts that this functor is represented by the stratified family; the gluing combines the gluing of points of the scheme $M_C$ over a basic open cover with the local comparison of strata points supplied by [`CerednikDrinfeld.QM.IsFineModuli.exists_strata_point_locally_corr_of_span_eq_top`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_strata_point_locally_corr_of_span_eq_top) and the equivalence and descent properties of the relation `Rel`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_PR_existsUnique_map_eq_of_span_eq_top.lean

import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.RigidifiedPairClass.PR.existsUnique_map_eq_of_span_eq_top
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))

    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })

    (hx2 : (∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
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
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                    Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T ψT hψT u ρ hd h0).1))
    (hx3 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T ψT hψT u ρ hd h0 = x))
    (hx4 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T ψT hψT u ρ hd h0 = RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ)))

    (hxM : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
        (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
        (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf d T ψT hψT u ρ hd h0).1 ≫ ξ d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (hmap : RigidifiedPairClass.MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) :
    ∀ (A : Type) [CommRing A] [Algebra C A] (m : ℕ) (f : Fin m → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin m → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)]
        (s : ∀ i, (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).obj (B i)),
      (∀ (i j : Fin m) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
          [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
          (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).map (ρ₁.restrictScalars C) (s i) =
          (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).map (ρ₂.restrictScalars C) (s j)) →
      ∃! s₀ : (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).obj A,
        ∀ i, (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).map (IsScalarTower.toAlgHom C A (B i)) s₀ = s i := by sorry
