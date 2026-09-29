-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_strata_point_locally_corr_of_span_eq_top
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_strata_point_locally_corr_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/867e3ac5-aab6-5ead-a755-261ab19da540
-- title:
--   Zariski gluing of presented stratum points up to r-power correspondence
-- statement:
--   Throughout, $\mathbb{H}[\mathbb{Q},a,b]$ denotes the rational quaternion algebra attached to $a,b\in\mathbb{Q}$, and for a commutative ring $R$ and morphisms $g:Y\to B$, $f:X\to B$ of schemes, `SchemeHomOver g f` denotes the type of morphisms $\varphi:Y\to X$ with $\varphi$ followed by $f$ equal to $g$.
--
--   **Quaternionic data.** Primes $r$ and $\bar r$ with $\bar r\neq r$, a nonzero $N$ with $r\nmid N$, and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b r rbar` holds: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit if and only if $v$ contains $r$ or $\bar r$. Further, a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order (it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and every order containing it equals it), with the hypothesis `hΛℤ` that every rational integer lies in $\Lambda$, and a map $\mathrm{coord}:\Lambda\to W(\mathbb{F}_{r^2})^2$ satisfying `IsOrderCoord Λ r coord`: it is additive and injective, sends $1$ to $(1,0)$, is multiplicative for the twisted rule $(\alpha_1,\alpha_2)(\beta_1,\beta_2)=(\alpha_1\beta_1+r\,\alpha_2\sigma(\beta_2),\ \alpha_1\beta_2+\alpha_2\sigma(\beta_1))$ with $\sigma$ the Witt-vector Frobenius, has dense image modulo every power of $r$ in both coordinates, and matches reduced traces with the trace $\alpha_1+\sigma(\alpha_1)$.
--
--   **Coefficients.** A commutative ring $\mathcal{O}$ and $\pi\in\mathcal{O}$ with $(r)=(\pi)$ as ideals of $\mathcal{O}$, an $\mathcal{O}$-algebra $O^{\mathrm{nr}}$, and a fake elliptic curve $A_0$ of type $(\Lambda,N)$ over $O^{\mathrm{nr}}/\pi O^{\mathrm{nr}}$ (an abelian scheme with commutative relative group law, two-dimensional fibres, a $\Lambda$-action compatible with the law and with reduced traces, and a level-$N$ datum).
--
--   **Fine moduli data.** An integer $n$ with $3\le n$ and $r\nmid n$, a scheme $M$ with a morphism $f_M:M\to\operatorname{Spec}\mathcal{O}$, and a rule $\mathrm{ptF}$ which to every commutative ring $S$, every $s:\operatorname{Spec} S\to\operatorname{Spec}\mathcal{O}$ and every pair $u$ consisting of a fake elliptic curve of type $(\Lambda,N)$ over $S$ with a full level-$n$ structure assigns a section of $f_M$ over $s$; the hypothesis `hM` states `IsFineModuli Λ N n M fM ptF`, i.e. $\mathrm{ptF}$ is invariant under isomorphism, compatible with pullback along ring maps, surjective onto sections, and injective up to isomorphism.
--
--   **Base ring.** A noetherian $\mathcal{O}$-algebra $C$ in which the image of $\pi$ is nilpotent, together with an $\mathcal{O}$-algebra map $\psi:O^{\mathrm{nr}}\to C$. Write $M_C$ for the fibre product of $f_M$ with $\operatorname{Spec}(\mathcal{O}\to C)$.
--
--   **Strata and their point rule.** A family of schemes $X_d$, $d\in\mathbb{N}$, with morphisms $\xi_d:X_d\to M_C$, and a rule $\mathrm{ptX}$ which, for every $d$, every $C$-algebra $T$ that is also an $\mathcal{O}$-algebra compatibly, every $\psi_T:O^{\mathrm{nr}}\to T$ equal to $\psi$ followed by $C\to T$, every full-level-$n$ object $u$ over $T$, and every rigidification $\rho$ of the underlying curve of $u$ with respect to $r,\pi,A_0,\psi_T$ (data consisting of a curve $E_b$ over $T/\pi$ pulled back from $u$, a curve $A_b$ over $T/\pi$ pulled back from $A_0$ along the induced map, an exponent $\rho.d$, and mutually inverse maps $\varphi,\varphi'$ forming an isogeny pair of degree $r^{\rho.d}$ between $E_b$ and $A_b$ preserving the level subscheme) with $\rho.d=d$ and with $\pi$ mapping to $0$ in $T$, produces a $T$-point of $X_d$ over $M_C$, namely a morphism $\operatorname{Spec} T\to X_d$ whose composite with $\xi_d$ followed by the projection $M_C\to\operatorname{Spec} C$ is $\operatorname{Spec}(C\to T)$. Four hypotheses constrain this rule: `hx2`, naturality, asserting that for a $C$-algebra map $\varphi:T\to T'$, objects $u$ over $T$ and $u'$ over $T'$ with a pullback morphism $g$ of the underlying curves matching the level points, and rigidifications $\rho$, $\rho'$ of the same exponent related by `Rigidification.IsPullbackVia` along $\varphi$ and $g$, the point attached to $(u',\rho')$ is $\operatorname{Spec}\varphi$ followed by the point attached to $(u,\rho)$; `hx3`, surjectivity, asserting that every $T$-point of $X_d$ over $M_C$ arises from some pair $(u,\rho)$ of exponent $d$; `hx4`, the injectivity criterion, asserting that two such points coincide if and only if there are an isomorphism $i$ of the underlying curves over the base compatible with the group law, the $\Lambda$-action, the level subscheme and the level-$n$ point (`WithFullLevel.IsoVia`), together with morphisms $i_b:\rho.E_b\to\rho'.E_b$ over the base compatible with the reduction maps and $u_A:\rho'.A_b\to\rho.A_b$ a pullback along the identity compatible with the maps to $A_0$, such that $i_b$ followed by $\rho'.\varphi$ followed by $u_A$ equals $\rho.\varphi$ (no $r$-power scalar being allowed here); and `hxM`, asserting that the $M_C$-coordinate of the point attached to $(u,\rho)$, that is its composite with $\xi_d$ followed by the projection $M_C\to M$, is the fine moduli point $\mathrm{ptF}$ of $u$.
--
--   **Cover data.** A $C$-algebra $A$, an integer $m$ and elements $f_0,\dots,f_{m-1}\in A$ generating the unit ideal, and for each $i$ a $C$-algebra $B_i$ which is the localisation of $A$ away from $f_i$, compatibly with the tower $C\to A\to B_i$. Further, for each $i$ a morphism $t_i:\operatorname{Spec} B_i\to M_C$ lying over $\operatorname{Spec}(C\to B_i)$ (hypothesis `ht`), an exponent $d(i)\in\mathbb{N}$, and a morphism $x_i:\operatorname{Spec}(B_i/\pi B_i)\to X_{d(i)}$ such that $x_i$ followed by $\xi_{d(i)}$ equals the reduction morphism $\operatorname{Spec}(B_i/\pi B_i)\to\operatorname{Spec} B_i$ followed by $t_i$ (hypothesis `hx`); finally a morphism $t_0:\operatorname{Spec} A\to M_C$ lying over $\operatorname{Spec}(C\to A)$ (hypothesis `ht₀`) whose restriction along $A\to B_i$ is $t_i$ for every $i$ (hypothesis `ht₀t`).
--
--   **Overlap compatibility `hover`.** For all indices $i,j$, every $C$-algebra $D$ which is a localisation of $A$ away from $f_if_j$ (compatibly with the tower), all $A$-algebra maps $\sigma_1:B_i\to D$ and $\sigma_2:B_j\to D$, and all ring maps $\tau_1:B_i/\pi\to D/\pi$ and $\tau_2:B_j/\pi\to D/\pi$ induced by $\sigma_1$, $\sigma_2$ on the quotients, there exist an integer $m_L$ and elements $g_0,\dots,g_{m_L-1}$ of $D/\pi$ generating the unit ideal such that for every $k$ there are: a localisation $L$ of $D/\pi$ away from $g_k$ carrying compatible $C$- and $\mathcal{O}$-algebra structures in which the image of $\pi$ is zero; full-level-$n$ objects $v,v'$ over $L$; rigidifications $\varrho$ of $v$ and $\varrho'$ of $v'$ with respect to the structural map $O^{\mathrm{nr}}\to L$ induced by $\psi$, of exponents $d(i)$ and $d(j)$ respectively; an isomorphism $i_0$ of the underlying curves over the base satisfying `WithFullLevel.IsoVia`; and the $r$-power correspondence clause, namely morphisms $i_b:\varrho.E_b\to\varrho'.E_b$ compatible with the reduction maps and with $i_0$, and $u_A:\varrho'.A_b\to\varrho.A_b$ a pullback along the identity compatible with the maps to $A_0$, together with integers $i_1,j_1$ such that $i_b$ followed by $\varrho'.\varphi$, $u_A$ and the action of $r^{i_1}$ on $\varrho.A_b$ equals $\varrho.\varphi$ followed by the action of $r^{j_1}$; and such that the point of $X_{d(i)}$ attached to $(v,\varrho)$ is the restriction along $D/\pi\to L$ of $\operatorname{Spec}\tau_1$ followed by $x_i$, while the point of $X_{d(j)}$ attached to $(v',\varrho')$ is the restriction along $D/\pi\to L$ of $\operatorname{Spec}\tau_2$ followed by $x_j$.
--
--   **Conclusion.** Under these hypotheses there exist an exponent $e\in\mathbb{N}$, a morphism $x_0:\operatorname{Spec}(A/\pi A)\to X_e$, and a proof that $x_0$ followed by $\xi_e$ equals the reduction morphism $\operatorname{Spec}(A/\pi A)\to\operatorname{Spec} A$ followed by $t_0$, with the following property. For every index $i$ and every ring map $\tau:A/\pi A\to B_i/\pi B_i$ induced by $A\to B_i$ on the quotients, there are an integer $m_L$ and elements $g_0,\dots,g_{m_L-1}$ of $B_i/\pi B_i$ generating the unit ideal such that for each $k$ there exist: a localisation $L$ of $B_i/\pi B_i$ away from $g_k$, equipped with compatible $C$- and $\mathcal{O}$-algebra structures in which the image of $\pi$ is zero; full-level-$n$ objects $v,v'$ over $L$; rigidifications $\varrho$ of $v$ with $\varrho.d=e$ and $\varrho'$ of $v'$ with $\varrho'.d=d(i)$, both with respect to the map $O^{\mathrm{nr}}\to L$ induced by $\psi$; an isomorphism $i_0:v.A\xrightarrow{\sim}v'.A$ over the base satisfying `WithFullLevel.IsoVia`; the $r$-power correspondence clause, namely morphisms $i_b:\varrho.E_b\to\varrho'.E_b$ with $i_b$ followed by $\varrho'.g_b$ equal to $\varrho.g_b$ followed by $i_0$ and $i_b$ compatible with the structure morphisms, a morphism $u_A:\varrho'.A_b\to\varrho.A_b$ which is a pullback along the identity ring map and satisfies $u_A$ followed by $\varrho.g_A$ equal to $\varrho'.g_A$, and integers $i_1,j_1$ with $i_b$ followed by $\varrho'.\varphi$, $u_A$ and the action of $r^{i_1}$ equal to $\varrho.\varphi$ followed by the action of $r^{j_1}$; and, finally, the two identifications of points: the point of $X_e$ attached to $(v,\varrho)$ equals $\operatorname{Spec}(B_i/\pi\to L)$ followed by ($\operatorname{Spec}\tau$ followed by $x_0$), and the point of $X_{d(i)}$ attached to $(v',\varrho')$ equals $\operatorname{Spec}(B_i/\pi\to L)$ followed by $x_i$.
--
--   Thus a single stratum index $e$ and a single point $x_0$ over $A/\pi A$ are produced, lying over $t_0$, whose restriction to each member of the given cover agrees with $x_i$ after a further cover of $\operatorname{Spec}(B_i/\pi B_i)$ by basic opens, up to isomorphism with level and an $r$-power correspondence of rigidifications.
--
--   This is the existence half of the Zariski-sheaf property for the functor of rigidified pairs of fake elliptic curves, presented through the degree strata $X_d$ over the base change $M_C$ of the level-$n$ fine moduli scheme: data given over a finite basic-open cover of $\operatorname{Spec}(A/\pi A)$ and agreeing on overlaps up to $r$-power correspondence is glued to a single presented point over $A/\pi A$. It feeds the uniqueness-and-existence statement [`CerednikDrinfeld.QM.RigidifiedPairClass.PR.existsUnique_map_eq_of_span_eq_top`](thm.html#CerednikDrinfeld.QM.RigidifiedPairClass.PR.existsUnique_map_eq_of_span_eq_top), and through it the representability of the functor of rigidified fake elliptic curves by the formal upper half plane charts in the Čerednik–Drinfeld comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_strata_point_locally_corr_of_span_eq_top.lean

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

theorem CerednikDrinfeld.QM.IsFineModuli.exists_strata_point_locally_corr_of_span_eq_top
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
    (ptX : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
              (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
              ρ.d = d → algebraMap C T (algebraMap 𝒪 C π) = 0 → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
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
                  (ptX d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                    Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (ptX d T ψT hψT u ρ hd h0).1))
    (hx3 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  ptX d T ψT hψT u ρ hd h0 = x))
    (hx4 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                (ptX d T ψT hψT u ρ hd h0 = ptX d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ)))

    (hxM : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
        (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
        (ptX d T ψT hψT u ρ hd h0).1 ≫ ξ d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (A : Type) [CommRing A] [Algebra C A]
    (m : ℕ) (f : Fin m → A) (hf : Ideal.span (Set.range f) = ⊤)
    (B : Fin m → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)] [∀ i, IsScalarTower C A (B i)]
    [∀ i, IsLocalization.Away (f i) (B i)]
    (t : ∀ i, Spec (CommRingCat.of (B i)) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (ht : ∀ i, t i ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = Spec.map (CommRingCat.ofHom (algebraMap C (B i))))
    (d : Fin m → ℕ) (x : ∀ i, Spec (CommRingCat.of ((B i) ⧸ Ideal.span {algebraMap C (B i) (algebraMap 𝒪 C π)})) ⟶ X (d i))
    (hx : ∀ i, x i ≫ ξ (d i) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C (B i) (algebraMap 𝒪 C π)}))) ≫ t i)
    (t₀ : Spec (CommRingCat.of A) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (ht₀ : t₀ ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = Spec.map (CommRingCat.ofHom (algebraMap C A)))
    (ht₀t : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap A (B i))) ≫ t₀ = t i)

    (hover : ∀ (i j : Fin m) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
        [IsLocalization.Away (f i * f j) D] (σ₁ : B i →ₐ[A] D) (σ₂ : B j →ₐ[A] D)
        (τ₁ : ((B i) ⧸ Ideal.span {algebraMap C (B i) (algebraMap 𝒪 C π)}) →+* ((D) ⧸ Ideal.span {algebraMap C (D) (algebraMap 𝒪 C π)})) (_ : τ₁.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (σ₁ : B i →+* D))
        (τ₂ : ((B j) ⧸ Ideal.span {algebraMap C (B j) (algebraMap 𝒪 C π)}) →+* ((D) ⧸ Ideal.span {algebraMap C (D) (algebraMap 𝒪 C π)})) (_ : τ₂.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (σ₂ : B j →+* D)),
        (∃ (mL : ℕ) (g : Fin mL → ((D) ⧸ Ideal.span {algebraMap C (D) (algebraMap 𝒪 C π)})), Ideal.span (Set.range g) = ⊤ ∧
          ∀ k : Fin mL,
            ∃ (L : Type) (_ : CommRing L) (_ : Algebra ((D) ⧸ Ideal.span {algebraMap C (D) (algebraMap 𝒪 C π)}) L) (_ : IsLocalization.Away (g k) L) (_ : Algebra C L)
              (_ : IsScalarTower C ((D) ⧸ Ideal.span {algebraMap C (D) (algebraMap 𝒪 C π)}) L) (_ : Algebra 𝒪 L) (_ : IsScalarTower 𝒪 C L)
              (h0 : algebraMap C L (algebraMap 𝒪 C π) = 0)
              (v v' : FakeEllipticCurve.WithFullLevel Λ N n L)
              (ϱ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) v.1)
              (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) v'.1)
              (hϱ : ϱ.d = d i) (hϱ' : ϱ'.d = d j)
              (i₀ : v.1.A ≅ v'.1.A) (hi : i₀.hom ≫ v'.1.f = v.1.f) (_ : FakeEllipticCurve.WithFullLevel.IsoVia v v' i₀ hi)
              (_ : (∃ (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ.gb ≫ i₀.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
                  (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ.gA = ϱ'.gA)
                  (i₁ j₁ : ℕ),
                  ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)),
              (ptX (d i) L _ rfl v ϱ hϱ h0).1 = Spec.map (CommRingCat.ofHom (algebraMap ((D) ⧸ Ideal.span {algebraMap C (D) (algebraMap 𝒪 C π)}) L)) ≫ (Spec.map (CommRingCat.ofHom τ₁) ≫ x i) ∧
                (ptX (d j) L _ rfl v' ϱ' hϱ' h0).1 = Spec.map (CommRingCat.ofHom (algebraMap ((D) ⧸ Ideal.span {algebraMap C (D) (algebraMap 𝒪 C π)}) L)) ≫ (Spec.map (CommRingCat.ofHom τ₂) ≫ x j))) :
    ∃ (e : ℕ) (x₀ : Spec (CommRingCat.of ((A) ⧸ Ideal.span {algebraMap C (A) (algebraMap 𝒪 C π)})) ⟶ X e)
      (_ : x₀ ≫ ξ e = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C (A) (algebraMap 𝒪 C π)}))) ≫ t₀),
      ∀ (i : Fin m) (τ : ((A) ⧸ Ideal.span {algebraMap C (A) (algebraMap 𝒪 C π)}) →+* ((B i) ⧸ Ideal.span {algebraMap C (B i) (algebraMap 𝒪 C π)}))
        (_ : τ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (algebraMap A (B i))),
        (∃ (mL : ℕ) (g : Fin mL → ((B i) ⧸ Ideal.span {algebraMap C (B i) (algebraMap 𝒪 C π)})), Ideal.span (Set.range g) = ⊤ ∧
          ∀ k : Fin mL,
            ∃ (L : Type) (_ : CommRing L) (_ : Algebra ((B i) ⧸ Ideal.span {algebraMap C (B i) (algebraMap 𝒪 C π)}) L) (_ : IsLocalization.Away (g k) L) (_ : Algebra C L)
              (_ : IsScalarTower C ((B i) ⧸ Ideal.span {algebraMap C (B i) (algebraMap 𝒪 C π)}) L) (_ : Algebra 𝒪 L) (_ : IsScalarTower 𝒪 C L)
              (h0 : algebraMap C L (algebraMap 𝒪 C π) = 0)
              (v v' : FakeEllipticCurve.WithFullLevel Λ N n L)
              (ϱ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) v.1)
              (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) v'.1)
              (hϱ : ϱ.d = e) (hϱ' : ϱ'.d = d i)
              (i₀ : v.1.A ≅ v'.1.A) (hi : i₀.hom ≫ v'.1.f = v.1.f) (_ : FakeEllipticCurve.WithFullLevel.IsoVia v v' i₀ hi)
              (_ : (∃ (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ.gb ≫ i₀.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
                  (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ.gA = ϱ'.gA)
                  (i₁ j₁ : ℕ),
                  ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)),
              (ptX (e) L _ rfl v ϱ hϱ h0).1 = Spec.map (CommRingCat.ofHom (algebraMap ((B i) ⧸ Ideal.span {algebraMap C (B i) (algebraMap 𝒪 C π)}) L)) ≫ (Spec.map (CommRingCat.ofHom τ) ≫ x₀) ∧
                (ptX (d i) L _ rfl v' ϱ' hϱ' h0).1 = Spec.map (CommRingCat.ofHom (algebraMap ((B i) ⧸ Ideal.span {algebraMap C (B i) (algebraMap 𝒪 C π)}) L)) ≫ (x i)) := by sorry
