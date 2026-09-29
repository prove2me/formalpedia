-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem
-- name    : CerednikDrinfeld.QM.RigidifiedPairClass.exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/86173330-5102-5613-9222-80c3134eaa39
-- title:
--   Equal `ptR`-class implies isomorphism up to an r-power shift
-- statement:
--   The setting is the Čerednik–Drinfeld rigidified-pair model. Fix natural numbers $r$ (prime) and $N \neq 0$ with $r \nmid N$, and a prime $\bar r \neq r$.
--
--   **Arithmetic data.** A commutative ring $\mathcal O$ with an element $\pi$ such that $\mathrm{span}\{r\} = \mathrm{span}\{\pi\}$ as ideals of $\mathcal O$ (so $\pi$ generates the same ideal as the rational prime $r$), and a commutative $\mathcal O$-algebra $\mathrm{Onr}$. Rationals $a,b$ with `hBq : IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ has all its nonzero elements invertible exactly when $v$ contains $r$ or $\bar r$. A $\mathbb Z$-submodule $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ which is a maximal order (it contains $1$, is closed under multiplication, spans $\mathbb H[\mathbb Q,a,b]$ over $\mathbb Q$, is finitely generated, and is maximal among such orders), together with `hΛℤ`, the requirement that every rational integer lies in $\Lambda$. A map $\mathrm{coord} : \Lambda \to \mathrm{Zp2}\,r \times \mathrm{Zp2}\,r$ satisfying `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, satisfies the twisted multiplication rule $\mathrm{coord}(mm') = (\alpha\alpha' + r\,\beta\,F(\beta'),\ \alpha\beta' + \beta F(\alpha'))$ for $\mathrm{coord}(m) = (\alpha,\beta)$, $\mathrm{coord}(m') = (\alpha',\beta')$ and $F$ the Witt-vector Frobenius, is injective, has image dense modulo every power of $r$ in each coordinate, and matches reduced traces in the first coordinate. Finally a fake elliptic curve $A_0$ over $\mathrm{Onr}/\pi$ with $\Lambda$-action and level-$N$ structure.
--
--   **Moduli data.** A natural number $n$ with $3 \le n$ and $r \nmid n$, a scheme $M$ with a morphism $f_M : M \to \operatorname{Spec} \mathcal O$, and a point rule $\mathrm{ptF}$ assigning to every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec} \mathcal O$ and every pair $u = (E,\text{full level }n)$ over $S$ an $M$-point over $s$; the hypothesis `hM : IsFineModuli Λ N n M fM ptF` states that $\mathrm{ptF}$ is invariant under isomorphisms of such pairs, compatible with base change along ring maps, surjective and injective up to isomorphism (four clauses).
--
--   **Deformation data.** A noetherian commutative $\mathcal O$-algebra $C$ in which the image of $\pi$ is nilpotent, and an $\mathcal O$-algebra map $\psi : \mathrm{Onr} \to C$. Write $M_C$ for the fibre product of $f_M$ with $\operatorname{Spec} C \to \operatorname{Spec}\mathcal O$. Strata: a family of schemes $X d$ ($d \in \mathbb N$) with morphisms $\xi d : X d \to M_C$; a rule $t_M$ assigning to each $C$-algebra $T$ and each pair $u$ over $T$ a point of $M_C$ over $\operatorname{Spec} T \to \operatorname{Spec} C$; and a rule $\mathrm{xOf}$ which, for each $T$ that is simultaneously a $C$-algebra and an $\mathcal O$-algebra compatibly, each $\psi_T$ equal to $\psi$ followed by $C \to T$, each $u$ over $T$ and each rigidification $\rho$ of $u.1$, produces a morphism $\operatorname{Spec}(T/\pi T) \to X (\rho.d)$ whose composition with $\xi(\rho.d)$ is the reduction map followed by $t_M\,T\,u$. Here a rigidification $\rho$ of a fake elliptic curve $E$ over $T$ consists of: a curve $\rho.E_b$ over $T/\pi$ together with $\rho.g_b$ exhibiting it as the reduction of $E$; a curve $\rho.A_b$ over $T/\pi$ together with $\rho.g_A$ exhibiting it as the base change of $A_0$ along the map induced by $\psi_T$; an integer $\rho.d$; and morphisms $\rho.\varphi : \rho.E_b \to \rho.A_b$, $\rho.\varphi'$ in the opposite direction forming an isogeny pair of degree $r^{\rho.d}$ with $\rho.\varphi$ level-preserving.
--
--   **Compatibility hypotheses.** `hmap : MapCompat …` asserts that the relation `Rel` defining the quotient functor is preserved by the transport `Pt.map φ` of points along any $C$-algebra map. `htM` asserts that the $M$-coordinate of $t_M\,T\,u$ (its composition with the first projection of $M_C$) is the fine-moduli point $\mathrm{ptF}\,T\,u$. `hx3` asserts, for every $d$ and every $T$ as above in which the image of $\pi$ vanishes, that every point of $X d$ over $\operatorname{Spec} T$ arises as $\mathrm{ptX}\,d\,T\,\psi_T\,u\,\rho$ for some pair $u$ over $T$ and some rigidification $\rho$ with $\rho.d = d$. `hx4` asserts, in the same situation, that $\mathrm{ptX}\,d\,T\,\psi_T\,u\,\rho = \mathrm{ptX}\,d\,T\,\psi_T\,u'\,\rho'$ holds if and only if there are an isomorphism $i : u.1.A \cong u'.1.A$ over $T$ with $\mathrm{IsoVia}\,u\,u'\,i$ (compatibility with the group law, with the $\Lambda$-action, with the level subscheme in both directions, and matching of the level-$n$ points), a morphism $i_b : \rho.E_b.A \to \rho'.E_b.A$ with $i_b \gg \rho'.g_b = \rho.g_b \gg i$ and $i_b$ over $T/\pi$, and a morphism $u_A : \rho'.A_b.A \to \rho.A_b.A$ exhibiting $\rho'.A_b$ as a base change of $\rho.A_b$ along the identity with $u_A \gg \rho.g_A = \rho'.g_A$, such that $i_b \gg \rho'.\varphi \gg u_A = \rho.\varphi$ exactly, with no $r$-power correction. `hxM` asserts that the $M$-coordinate of $\mathrm{ptX}\,d\,T\,\psi_T\,u\,\rho$ (its composition with $\xi d$ and with the first projection of $M_C$) is again $\mathrm{ptF}\,T\,u$. `hxOf` asserts naturality of $\mathrm{xOf}$: for $C$-algebras $S, S'$ with compatible $\mathcal O$-structures, a $C$-algebra map $\varphi : S \to S'$, pairs $u$ over $S$ and $u'$ over $S'$, rigidifications $\rho$, $\rho'$ of $u.1$ and $u'.1$, and a morphism $g : u'.1.A \to u.1.A$ exhibiting $u'.1$ as the base change of $u.1$ along $\varphi$ which carries the level-$n$ point of $u'$ to that of $u$ and which realises $\rho'$ as the base change of $\rho$, one has $\rho'.d = \rho.d$ and, after transport along that equality, $\mathrm{xOf}\,S'\,u'\,\rho'$ equals $\operatorname{Spec}$ of the induced map on the $\pi$-quotients followed by $\mathrm{xOf}\,S\,u\,\rho$.
--
--   **Conclusion.** For every type $S$ which is a commutative ring, a $C$-algebra and an $\mathcal O$-algebra with the scalar tower $\mathcal O \to C \to S$, every $\mathcal O$-algebra map $\psi_S : \mathrm{Onr} \to S$ equal to $\psi$ followed by $C \to S$, under the hypothesis `hSc` that every idempotent of $S$ is $0$ or $1$, and for all pairs $u, u'$ over $S$ with rigidifications $\rho$ of $u.1$ and $\rho'$ of $u'.1$: if
--   $$\mathrm{ptR}\,S\,\psi_S\,u\,\rho = \mathrm{ptR}\,S\,\psi_S\,u'\,\rho'$$
--   in the quotient $\mathrm{PR}(S)$ — that is, if the classes of the points with $M_C$-coordinate $t_M\,S\,u$, index $\rho.d$ and $X$-coordinate $\mathrm{xOf}\,S\,\psi_S\,u\,\rho$, respectively $t_M\,S\,u'$, $\rho'.d$, $\mathrm{xOf}\,S\,\psi_S\,u'\,\rho'$, agree — then there exist:
--
--   - an isomorphism $i : u.1.A \cong u'.1.A$ with $i \gg u'.1.f = u.1.f$ such that $\mathrm{IsoVia}\,u\,u'\,i$ holds (i.e. $i$ is compatible with the relative group laws, intertwines the $\Lambda$-actions, matches the level-$N$ subschemes in both directions, and carries the full level-$n$ point of $u$ to that of $u'$);
--
--   - a morphism $i_b : \rho.E_b.A \to \rho'.E_b.A$ with $i_b \gg \rho'.g_b = \rho.g_b \gg i$ and $i_b \gg \rho'.E_b.f = \rho.E_b.f$;
--
--   - a morphism $u_A : \rho'.A_b.A \to \rho.A_b.A$ exhibiting $\rho'.A_b$ as the base change of $\rho.A_b$ along the identity ring map, with $u_A \gg \rho.g_A = \rho'.g_A$;
--
--   - natural numbers $i_1, j_1$ such that
--   $$i_b \gg \rho'.\varphi \gg u_A \gg \rho.A_b.\mathrm{act}\,[r^{i_1}] \;=\; \rho.\varphi \gg \rho.A_b.\mathrm{act}\,[r^{j_1}],$$
--   where $[m]$ denotes the element of $\Lambda$ given by the rational integer $m$, available by `hΛℤ`.
--
--   Thus the comparison of the two rigidifications is asserted only up to a single global pair of $r$-power multiplications on $\rho.A_b$, and not as the shift-free equality which `hx4` postulates for the stratum points $\mathrm{ptX}$ over rings killing $\pi$.
--
--   This is the injectivity half of the representability of the functor of rigidified fake elliptic curves with full level $n$ by the strata $X_d$ in the Čerednik–Drinfeld uniformisation: over a base with no nontrivial idempotents, two rigidified pairs with the same class in $\mathrm{PR}$ are isomorphic as pairs with level structure, the rigidifications corresponding up to one $r$-power shift. It is used in the construction of the functor represented by the strata, [`CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.RigidifiedPairClass.exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem
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
    (hmap : RigidifiedPairClass.MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf)

    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (u : FakeEllipticCurve.WithFullLevel Λ N n T),
        (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (hx3 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = x))

    (hx4 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ)))

    (hxM : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
        (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
        ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0).1 ≫ ξ d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (hxOf : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
        (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
        (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
        (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
        FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
          ∃ hd : ρ'.d = ρ.d, (xOf S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ').1 ≫ eqToHom (congrArg X hd) =
            Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf S ψS hψS u ρ).1) :
    (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
          (hSc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1),
          (RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap) S ψS hψS u ρ = (RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap) S ψS hψS u' ρ' →
            ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
              ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by sorry
