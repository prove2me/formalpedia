-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback
-- name    : CerednikDrinfeld.QM.RigidifiedPairClass.exists_stratumPoint_of_forall_representsOn_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/77a12c4f-0741-53fc-a551-3a3903d864e4
-- title:
--   Strata points of rigidified fake elliptic curves
-- statement:
--   Throughout, $\mathbb H = \mathbb H[\mathbb Q,a,b]$ denotes the quaternion algebra attached to $a,b\in\mathbb Q$, and a *fake elliptic curve* over a commutative ring $S$ (`FakeEllipticCurve Λ N S`) is the structure consisting of a scheme $A$ over $\operatorname{Spec} S$ which is smooth and proper with connected two-dimensional fibres, carrying a commutative relative group law, an action of $\Lambda$ which is additive, multiplicative and satisfies the prescribed trace condition on tangent spaces, together with the level-$N$ data recorded by the structure (the scheme `C` and the morphism `lev`, and the further fields of the structure).
--
--   **Arithmetic data.** A prime $r$, a natural number $N\neq 0$ with $r\nmid N$, and a prime $\bar r\neq r$. A commutative ring $\mathcal O$ with an element $\pi$ such that the ideals $(r)$ and $(\pi)$ of $\mathcal O$ coincide, and an $\mathcal O$-algebra $O^{\mathrm{nr}}$. Rationals $a,b$ with `IsIndefiniteRamifiedExactlyAt a b r rbar`: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathbb Z$ every nonzero element of $\mathbb H\otimes_{\mathbb Q}\mathbb Q_v$ is a unit if and only if $r\in v$ or $\bar r\in v$. A $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H$ which is a maximal order (it contains $1$, is closed under multiplication, spans $\mathbb H$ over $\mathbb Q$, is finitely generated, and is maximal among submodules with these properties), and which contains every rational integer ($h\Lambda\mathbb Z$). A map $\mathrm{coord}:\Lambda\to \mathbb Z_{r^2}\times\mathbb Z_{r^2}$ (where $\mathbb Z_{r^2}=$ `Zp2 r` is the Witt ring of $\mathbb F_{r^2}$) satisfying `IsOrderCoord Λ r coord`: additivity, $1\mapsto(1,0)$, the Frobenius-twisted multiplication rule of the definition, injectivity, density of the image modulo every power of $r$, and compatibility with reduced traces.
--
--   **Moduli data.** A fake elliptic curve $A_0$ over $O^{\mathrm{nr}}/\pi O^{\mathrm{nr}}$. A natural number $n$ with $3\le n$ and $r\nmid n$; a scheme $M$ with $f_M:M\to\operatorname{Spec}\mathcal O$ and a point rule $\mathrm{ptF}$ assigning to each ring $S$, each $s:\operatorname{Spec} S\to\operatorname{Spec}\mathcal O$ and each $u\in$ `WithFullLevel Λ N n S` (a fake elliptic curve together with a full level-$n$ structure) a section of $f_M$ over $s$; the hypothesis $hM$ states `IsFineModuli Λ N n M fM ptF`, i.e. $\mathrm{ptF}$ is invariant under isomorphism of level-$n$ structures, compatible with base change along ring maps, surjective onto sections, and injective up to isomorphism.
--
--   **Deformation data.** A noetherian $\mathcal O$-algebra $C$ in which the image of $\pi$ is nilpotent, and an $\mathcal O$-algebra map $\psi:O^{\mathrm{nr}}\to C$. Write $\bar C=C/(\pi)$. A fake elliptic curve $\mathfrak A$ over $\bar C$ together with $g_{\mathfrak A}:\mathfrak A.A\to A_0.A$ such that $h\mathfrak A$ holds: $\mathfrak A$ is the pullback of $A_0$ along `residueLeg π ψ` $:O^{\mathrm{nr}}/\pi\to\bar C$ via $g_{\mathfrak A}$, in the sense of `FakeEllipticCurve.IsPullbackVia` (the square of structure morphisms is cartesian, and $g_{\mathfrak A}$ is compatible with the group laws, with the $\Lambda$-actions, and carries level points to level points).
--
--   **Strata data.** A family of schemes $\bar X_d$ ($d\in\mathbb N$) with morphisms $\bar q_d:\bar X_d\to M_{\bar C}:=M\times_{\operatorname{Spec}\mathcal O}\operatorname{Spec}\bar C$, and charts $\kappa$: for every $d$, every ring $S$ that is a $\bar C$-algebra and an $\mathcal O$-algebra in a compatible tower, every $u\in$ `WithFullLevel Λ N n S`, every fake elliptic curve $A$ over $S$ exhibited by $g_A$ as the pullback of $\mathfrak A$ along $\bar C\to S$, and every $X$ with $\xi:X\to\operatorname{Spec} S$ together with a family $\mathrm{pt}$ of `PtFamily r d u.1 A ξ` satisfying `RepresentsOn r d u.1 A ξ pt` (so that $\xi$ represents the functor of degree-$r^d$ level-preserving isogeny pairs between base changes of $u.1$ and of $A$), a morphism $\kappa\to\bar X_d$ out of $X$.
--
--   The hypothesis $hB$ imposes, for each $d$, three gluing laws. (B1): each chart, followed by $\bar q_d$ and by the first projection of $M_{\bar C}$, equals $\xi$ followed by the fine moduli point $\mathrm{ptF}(S,\cdot,u)$, and followed by the second projection equals $\xi$ followed by $\operatorname{Spec}$ of the structure map $\bar C\to S$. (B2): for every scheme $T$ with $x:T\to\bar X_d$ and $t:T\to\operatorname{Spec} S$ satisfying the two corresponding compatibilities, there is a unique $y:T\to X$ with $y$ followed by the chart equal to $x$ and $y$ followed by $\xi$ equal to $t$. (B3): compatibility of the charts with base change along $S\to S'$ in the tower, for data $u,u'$ related by $g$ (a pullback of level structures with matching level points) and $A,A'$ related by $h_A$, given $e:X'\to X$ forming a cartesian square with $\xi',\xi$ over $\operatorname{Spec} S'\to\operatorname{Spec} S$ and given that the point families $\mathrm{pt}'$ and $\mathrm{pt}$ agree after composition with $e$ on all isogeny pairs over all further $S'$-algebras: then $e$ followed by the chart for $(u,A,\xi,\mathrm{pt})$ equals the chart for $(u',A',\xi',\mathrm{pt}')$.
--
--   The hypothesis $hloc$ (local representability) asserts that for every $d$ and every $S,u,A,g_A$ as above there exist $X$, a morphism $\xi:X\to\operatorname{Spec} S$ locally of finite presentation, and a family $\mathrm{pt}$ with `RepresentsOn r d u.1 A ξ pt`.
--
--   **Comparison and point rule on $M_C$.** A morphism $\iota:M_{\bar C}\to M_C:=M\times_{\operatorname{Spec}\mathcal O}\operatorname{Spec} C$ with $h\iota_1$: $\iota$ commutes with the first projections; and $h\iota_2$: $\iota$ followed by the second projection equals the second projection followed by $\operatorname{Spec}$ of $C\to\bar C$. A rule $t_M$ assigning to each $C$-algebra $T$ and each $u\in$ `WithFullLevel Λ N n T` a section of the second projection $M_C\to\operatorname{Spec} C$ over $\operatorname{Spec}(C\to T)$, with $ht_M$: the $M$-coordinate of $t_M(T,u)$ is the fine moduli point $\mathrm{ptF}$ of $u$ over $\operatorname{Spec} T\to\operatorname{Spec} C\to\operatorname{Spec}\mathcal O$.
--
--   **Conclusion.** Under these hypotheses there exists a rule $\mathrm{xOf}$ which assigns, to every $C$-algebra $T$ that is also an $\mathcal O$-algebra in a compatible tower, every $\mathcal O$-algebra map $\psi_T:O^{\mathrm{nr}}\to T$ equal to $\psi$ followed by $C\to T$, every $u\in$ `WithFullLevel Λ N n T` and every rigidification $\rho\in$ `FakeEllipticCurve.Rigidification r π A₀ ψT u.1` (the data of a reduction $\rho.E_b$ of $u.1$ modulo $\pi_T$ via $\rho.g_b$, a fake elliptic curve $\rho.A_b$ over $T/\pi_T$ exhibited by $\rho.g_A$ as the pullback of $A_0$ along the induced map of residue rings, an exponent $\rho.d$, and mutually inverse-up-to-$r^{\rho.d}$ morphisms $\rho.\varphi,\rho.\varphi'$ forming a level-preserving isogeny pair between $\rho.E_b$ and $\rho.A_b$), a morphism $x:\operatorname{Spec}(T/\pi_T)\to\bar X_{\rho.d}$ subject to the condition that $x$ followed by $\bar q_{\rho.d}\circ\iota$ equals $\operatorname{Spec}$ of the quotient map $T\to T/\pi_T$ followed by $t_M(T,u)$.
--
--   Writing $\mathrm{ptX}$ for the derived point rule `RigidifiedPairClass.ptX` of the model, formed from $\mathcal O,\pi,O^{\mathrm{nr}},\Lambda,A_0,n,C,\psi$, the second projection $M_C\to\operatorname{Spec} C$, the family $\bar X$, the morphisms $\bar q_d\circ\iota$, $t_M$ and $\mathrm{xOf}$ — so that $\mathrm{ptX}(d,T,\psi_T,u,\rho)$, defined when $\rho.d=d$ and when $\pi$ maps to $0$ in $T$, is the section of $(\bar q_d\circ\iota)$ followed by the second projection, over $\operatorname{Spec}(C\to T)$, whose underlying morphism is $\operatorname{Spec}$ of the identification $T/(0)\cong T$ followed by $\mathrm{xOf}(T,\psi_T,u,\rho)$ transported along $\rho.d=d$ — the rule $\mathrm{xOf}$ satisfies the following five assertions.
--
--   (1) *Naturality of $\mathrm{ptX}$.* For every $d$, every $T,T'$ as above, every $C$-algebra map $\varphi:T\to T'$, every $\psi_T$ as above with $\varphi\circ\psi_T$ equal to $\psi$ followed by $C\to T'$, every $u$ over $T$ and $u'$ over $T'$, rigidifications $\rho$ of $u.1$ over $\psi_T$ and $\rho'$ of $u'.1$ over $\varphi\circ\psi_T$, every $g:u'.1.A\to u.1.A$ exhibiting $u'.1$ as the pullback of $u.1$ along $\varphi$, with $\rho.d=d$, $\rho'.d=d$ and $\pi$ mapping to $0$ in both $T$ and $T'$: if the level-$n$ point of $u'$ corresponds to that of $u$ under $g$, and if $\rho'$ is the pullback of $\rho$ along $\varphi$ and $g$ in the sense of `Rigidification.IsPullbackVia` (there are morphisms $u_b,u_A$ exhibiting $\rho'.E_b,\rho'.A_b$ as pullbacks along the induced map of residue rings, compatible with $\rho.g_b,g$ and with $\rho.g_A$, with $\rho'.d=\rho.d$ and $u_b\circ\rho.\varphi=\rho'.\varphi\circ u_A$ in diagrammatic form), then the underlying morphism of $\mathrm{ptX}$ at $(d,T',\varphi\circ\psi_T,u',\rho')$ equals $\operatorname{Spec}\varphi$ followed by that of $\mathrm{ptX}$ at $(d,T,\psi_T,u,\rho)$.
--
--   (2) *Exhaustiveness.* For every $d$, every $T$ as above, every $\psi_T$ as above with $\pi$ mapping to $0$ in $T$, and every section $x$ of $(\bar q_d\circ\iota)$ followed by the second projection over $\operatorname{Spec}(C\to T)$, there exist $u\in$ `WithFullLevel Λ N n T`, a rigidification $\rho$ of $u.1$ over $\psi_T$ and an identification $\rho.d=d$ with $\mathrm{ptX}(d,T,\psi_T,u,\rho)=x$.
--
--   (3) *Rigidity.* For every $d$, $T$, $\psi_T$ as above with $\pi$ mapping to $0$ in $T$, all $u,u'$ over $T$ and rigidifications $\rho$ of $u.1$, $\rho'$ of $u'.1$ over $\psi_T$ with $\rho.d=\rho'.d=d$: the points $\mathrm{ptX}(d,T,\psi_T,u,\rho)$ and $\mathrm{ptX}(d,T,\psi_T,u',\rho')$ are equal if and only if there exist an isomorphism $i:u.1.A\cong u'.1.A$ over $\operatorname{Spec} T$ with `WithFullLevel.IsoVia u u' i hi` (compatibility with the group laws, with the $\Lambda$-actions, with factorisation through the level morphisms in both directions, and matching of the level-$n$ points), together with a morphism $i_b:\rho.E_b.A\to\rho'.E_b.A$ over $\operatorname{Spec}(T/\pi_T)$ satisfying $i_b$ followed by $\rho'.g_b$ equals $\rho.g_b$ followed by $i$, and a morphism $u_A:\rho'.A_b.A\to\rho.A_b.A$ exhibiting $\rho'.A_b$ as the pullback of $\rho.A_b$ along the identity ring map, with $u_A$ followed by $\rho.g_A$ equal to $\rho'.g_A$, such that $i_b$ followed by $\rho'.\varphi$ followed by $u_A$ equals $\rho.\varphi$.
--
--   (4) *Fine moduli coordinate.* For every $d$, $T$, $\psi_T$, $u$, $\rho$ with $\rho.d=d$ and $\pi$ mapping to $0$ in $T$, the underlying morphism of $\mathrm{ptX}(d,T,\psi_T,u,\rho)$, followed by $\bar q_d\circ\iota$ and by the first projection of $M_C$, equals the fine moduli point $\mathrm{ptF}(T,\operatorname{Spec}(\mathcal O\to T),u)$.
--
--   (5) *Naturality of $\mathrm{xOf}$.* For all $T,T'$ as above, every $C$-algebra map $\varphi:T\to T'$, every $\psi_T$ as above with $\varphi\circ\psi_T$ equal to $\psi$ followed by $C\to T'$, all $u$ over $T$, $u'$ over $T'$, rigidifications $\rho$ of $u.1$ over $\psi_T$ and $\rho'$ of $u'.1$ over $\varphi\circ\psi_T$, every $g$ exhibiting $u'.1$ as the pullback of $u.1$ along $\varphi$, and every identification $\rho'.d=\rho.d$: if the level-$n$ point of $u'$ corresponds to that of $u$ under $g$ and $\rho'$ is the pullback of $\rho$ along $\varphi$ and $g$, then $\mathrm{xOf}(T',\varphi\circ\psi_T,u',\rho')$, transported along the identification of strata indices, equals $\operatorname{Spec}$ of the induced map $T/\pi_T\to T'/\pi_{T'}$ (`RigidifiedPairClass.qmap`) followed by $\mathrm{xOf}(T,\psi_T,u,\rho)$. This clause is asserted without assuming that $\pi$ vanishes in $T$ or $T'$.
--
--   This is the construction of the point rule on the glued strata $\bar X_d$ of degree-$r^d$ isogeny pairs occurring in the Čerednik–Drinfeld description of a Shimura curve attached to the indefinite quaternion algebra ramified exactly at $r$ and $\bar r$: each rigidified fake elliptic curve with full level-$n$ structure over a $C$-algebra determines a point of the stratum indexed by its isogeny exponent, naturally in the base, exhaustively, and with an explicit criterion for two rigidified pairs to give the same point. It is used by [`CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified), where these strata laws are assembled into a functor on $C$-algebras representing rigidified curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel
import Definitions.Def_CerednikDrinfeld_QMIsogenyPairRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.RigidifiedPairClass.exists_stratumPoint_of_forall_representsOn_of_isPullback
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

    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)

    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
        (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
        (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB : ∀ d : ℕ,

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
          κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) =
              ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S))) ∧

      (∀ (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (T : Scheme.{0}) (x : T ⟶ Xbar d) (t : T ⟶ Spec (CommRingCat.of S)),
          x ≫ qbar d ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 →
          x ≫ qbar d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) = t ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)) →
            ∃! y : T ⟶ X, y ≫ κ d S u A gA hgA X ξ pt hX = x ∧ y ≫ ξ = t) ∧

      (∀ (S S' : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
          [CommRing S'] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S']
          [Algebra S S'] [IsScalarTower (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S S'] [IsScalarTower 𝒪 S S']
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (algebraMap S S') u.1 u'.1 g)
          (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (u.2.P).1)
          (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
          (A' : FakeEllipticCurve Λ N S') (hA : A'.A ⟶ A.A) (hhA : FakeEllipticCurve.IsPullbackVia (algebraMap S S') A A' hA)
          (hgA' : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S') 𝔄 A' (hA ≫ gA))
          (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S))
          (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
          (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
          (X' : Scheme.{0}) (ξ' : X' ⟶ Spec (CommRingCat.of S'))
          (pt' : FakeEllipticCurve.IsogenyPair.PtFamily r d u'.1 A' ξ')
          (hX' : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u'.1 A' ξ' pt')
          (e : X' ⟶ X),
          CategoryTheory.IsPullback e ξ' ξ (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
          (∀ (T : Type) [CommRing T] [Algebra S' T] [Algebra S T] [IsScalarTower S S' T]
              (E'' A'' : FakeEllipticCurve Λ N T)
              (gE'' : E''.A ⟶ u'.1.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) u'.1 E'' gE'')
              (gA'' : A''.A ⟶ A'.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S' T) A' A'' gA'')
              (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) u.1 E'' (gE'' ≫ g))
              (hgAA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' (gA'' ≫ hA))
              (φ : E''.A ⟶ A''.A) (φ' : A''.A ⟶ E''.A) (hφ : φ ≫ A''.f = E''.f)
              (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' φ φ') (hl : FakeEllipticCurve.PreservesLevel E'' A'' φ hφ),
              (pt' T E'' A'' gE'' hgE'' gA'' hgA'' φ φ' hφ hp hl).1 ≫ e =
                (pt T E'' A'' (gE'' ≫ g) hgE (gA'' ≫ hA) hgAA φ φ' hφ hp hl).1) →
            e ≫ κ d S u A gA hgA X ξ pt hX = κ d S' u' A' (hA ≫ gA) hgA' X' ξ' pt' hX'))

    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)

    (ι : Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hι₁ : ι ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (hι₂ : ι ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
      Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 C π}))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] (u : FakeEllipticCurve.WithFullLevel Λ N n T),
      (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
        (ptF T (Spec.map (CommRingCat.ofHom (algebraMap C T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) u).1) :
    ∃ xOf : (∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ Xbar ρ.d //
        x ≫ (qbar ρ.d ≫ ι) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 }),

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
                  ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                    Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T ψT hψT u ρ hd h0).1) ∧

      (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) ((qbar d ≫ ι) ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T ψT hψT u ρ hd h0 = x) ∧

      (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T ψT hψT u ρ hd h0 = (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T ψT hψT u' ρ' hd' h0 ↔
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ)) ∧

      (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
        (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
        ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) Xbar (fun d => qbar d ≫ ι) tM xOf) d T ψT hψT u ρ hd h0).1 ≫ (qbar d ≫ ι) ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1) ∧

      (∀ (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
          [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
          (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
          (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
          (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
          (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
          (hd : ρ'.d = ρ.d),
          (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
          FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
            (xOf T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ').1 ≫ eqToHom (congrArg Xbar hd) =
              Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf T ψT hψT u ρ).1) := by sorry
