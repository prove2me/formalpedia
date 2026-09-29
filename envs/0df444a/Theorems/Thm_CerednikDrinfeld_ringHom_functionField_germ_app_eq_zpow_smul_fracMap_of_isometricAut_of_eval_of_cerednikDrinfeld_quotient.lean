-- Prove2me | Theorems.Thm_CerednikDrinfeld_ringHom_functionField_germ_app_eq_zpow_smul_fracMap_of_isometricAut_of_eval_of_cerednikDrinfeld_quotient
-- name    : CerednikDrinfeld.ringHom_functionField_germ_app_eq_zpow_smul_fracMap_of_isometricAut_of_eval_of_cerednikDrinfeld_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/6bf66420-b904-55db-a716-2171fc66a282
-- title:
--   Galois equivariance of the Čerednik–Drinfeld evaluation embedding
-- statement:
--   *Arithmetic data.* Let $r$ be a prime, let $\mathcal O$ be a commutative domain of characteristic zero which is a discrete valuation ring (`hdvr`), let $\pi \in \mathcal O$ be irreducible (`hπ`), let $\mathcal O$ be $\pi$-adically complete (`hcomplete`), let the residue ring $\mathcal O/(\pi)$ have exactly $r$ elements (`hres`), and let $(r) = (\pi)$ as ideals of $\mathcal O$ (`hunr`). Let $K_0$ be a field of characteristic zero which is a fraction field of $\mathcal O$. Let $O^{\mathrm{nr}}$ be a commutative domain of characteristic zero and an $\mathcal O$-algebra, and let $\mathrm{Fr}$ be an $\mathcal O$-algebra automorphism of $O^{\mathrm{nr}}$, subject to: $O^{\mathrm{nr}}$ is $\pi$-adically complete (`hOnr_complete`), $(\pi)O^{\mathrm{nr}}$ is maximal (`hOnr_max`), every element of $O^{\mathrm{nr}}$ satisfies some monic polynomial over $\mathcal O$ modulo $\pi$ (`hOnr_alg`), every monic polynomial over $O^{\mathrm{nr}}$ of positive degree has a root modulo $\pi$ (`hOnr_closed`), and $\mathrm{Fr}(x) \equiv x^{r} \pmod{\pi}$ for all $x$ (`hFr`). Let $v\!\det : \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively) satisfy `hvdet`: $v\!\det(g) = n$ if and only if $\det g = u\pi^{n}$ in $K_0$ for some unit $u$ of $\mathcal O$.
--
--   *Group data.* Let $G$ be a group, $\sigma : G \to \mathrm{GL}_2(K_0)$ a homomorphism and $\Gamma \le G$ a subgroup such that some $z \in \Gamma$ has $\sigma z$ a scalar matrix $c \cdot 1$ with $v\!\det(\sigma z) = 2$ (`hcent`) and some $w \in \Gamma$ has $v\!\det(\sigma w) = 1$ (`hodd`). Let $\Gamma' \le G$ be the subgroup characterised by `hΓ'`: $x \in \Gamma'$ if and only if $x \in \Gamma$ and $v\!\det(\sigma x)$ is even. Let $\rho : G \to \mathrm{PGL}_2(K_0)$ be the homomorphism induced by $\sigma$ (`hρ`), and assume that the image $\rho(\Gamma')$ acts on the Bruhat–Tits tree of homothety classes of full $\mathcal O$-lattices in $K_0^2$ with finite vertex stabilisers (`hdisc`) and with finitely many orbits, in the form of a finite set $S$ of vertices meeting every orbit (`hcocpt`).
--
--   *The formal uniformisation datum.* Let $\mathcal X$ be a scheme and $f : \mathcal X \to \operatorname{Spec}\mathcal O$ a proper flat morphism. Let $\Theta$ assign, to every $\mathcal O$-algebra $B$ in which the image of $\pi$ is nilpotent, a map from pairs $(\psi, P)$ with $\psi : O^{\mathrm{nr}} \to_{\mathcal O} B$ an $\mathcal O$-algebra map and $P$ a Deligne datum over $B$ — that is, a family of $B$-submodules $P.\mathrm{line}(M) \subseteq B \otimes_{\mathcal O} M$, one for each full $\mathcal O$-lattice $M \subseteq K_0^2$, with invertible quotient, compatible with lattice inclusions, equivariant for scalar homotheties, and nondegenerate at every prime of $B$ — to a point of `Scheme.nilpPoints f` over $B$, i.e. a morphism $\operatorname{Spec} B \to \mathcal X$ over $\operatorname{Spec}\mathcal O$. Four hypotheses are imposed on $\Theta$: `hΘnat`, naturality in $B$ along $\mathcal O$-algebra maps; `hΘinv`, invariance under the twisted $\Gamma$-action, namely $\Theta(x') = \Theta(x)$ whenever $\gamma \in \Gamma$ and `OmegaNr.IsTwistedAct` holds for $\sigma\gamma$, which says that $x'_1 = x_1 \circ \mathrm{Fr}^{-v\!\det(\sigma\gamma)}$ and that, for every full lattice $M$, the line of $x'_2$ at $M$ is the preimage of the line of $x_2$ at $(\sigma\gamma)^{-1}M$ under the base-changed lattice isomorphism; `hΘfib`, which states for every algebraically closed field $k$ that is an $\mathcal O$-algebra with $\pi$ nilpotent and every $\psi : O^{\mathrm{nr}} \to_{\mathcal O} k$ both that every $k$-point of $f$ is of the form $\Theta(\psi, P)$ and that $\Theta(\psi, P) = \Theta(\psi, P')$ holds precisely when $(\psi,P)$ and $(\psi,P')$ are related by the twisted action of some $\gamma \in \Gamma$; and `hΘuniv`, which asserts the universal property of $\Theta$: for every scheme $T$ over $\operatorname{Spec}\mathcal O$ and every family $\rho'$ into the nilpotent points of $T$ that is natural in $B$ and invariant under the twisted $\Gamma$-action, there is a family $u$ from the nilpotent points of $f$ to those of $T$, natural in $B$, with $u \circ \Theta = \rho'$, and any family $u'$ with these two properties agrees with $u$.
--
--   *Analytic data.* Let $C$ be an algebraically closed field with a valuation into a linearly ordered commutative group with zero $\Gamma_0$, complete, and a $K_0$-algebra; let $R$ be a commutative ring which is an $\mathcal O$-algebra with $C$ an $R$-algebra, all compatible with the $\mathcal O$- and $K_0$-algebra structures on $C$ through the stated scalar towers. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi.\varpi \in K_0$ whose image in $C$ has valuation strictly between $0$ and $1$ and whose powers scale every nonzero element of $K_0$ from both sides. Let `hF` assert that $(\pi, \varpi, R)$ is an adic frame: $\pi$ is irreducible, $R \to C$ is injective with image exactly the elements of valuation $\le 1$, $R$ is $\pi$-adically complete, the elements of $K_0$ of valuation $\le 1$ in $C$ are exactly those coming from $\mathcal O$, the image of $K_0$ is closed in $C$, and $\pi$ and $\varpi.\varpi$ have the same image in $C$. Let $\psi_0 : O^{\mathrm{nr}} \to_{\mathcal O} R$ be an $\mathcal O$-algebra map. Assume further `hrk`: for $x$ with $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$; `hval`: every nonzero $\varepsilon \in \Gamma_0$ dominates the valuation of some nonzero element of $C$; `hex`: every point of the Drinfeld upper half plane $\Omega = C \setminus K_0$ lies in one of the affinoids $\{z : v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^{n}$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}\}$; and that `Omega.HolRingOf ϖ ρ`, the ring of functions $\Omega \to C$ that are uniform limits of pole-free bounded rational functions on each of these affinoids, is a domain.
--
--   *The uniformisation of $R$-points.* Let $\Phi$ send each adic point $x$ — a compatible system of Deligne data over the quotients $R/(\pi^{n+1})$ — to an $R$-point of $\mathcal X$ over $\operatorname{Spec}\mathcal O$. The hypothesis `hΦ` has four conjuncts: $\Phi(x)$ reduces modulo $\pi^{n+1}$ to $\Theta$ applied to the pair consisting of $\psi_0$ followed by the quotient map and the $n$-th component $x.\mathrm{pt}\,n$; $\Phi$ is surjective; $\Phi(x) = \Phi(x')$ if and only if $x' = x.\mathrm{act}(\sigma\gamma)$ for some $\gamma \in \Gamma'$, where the action pulls back each Deligne datum along $(\sigma\gamma)^{-1}$; and base change along $R \to C$ is injective on these $R$-points and hits every $C$-point of $\mathcal X$ over $\operatorname{Spec}\mathcal O$.
--
--   *The generic fibre and the evaluation map.* Let $s_C : \operatorname{Spec} C \to \operatorname{Spec}\mathcal O$ be the morphism induced by $\mathcal O \to K_0 \to C$ (`hsC`), and assume the pullback $\mathcal X_C = \mathcal X \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec} C$ is integral. Let $e$ be a ring homomorphism from the function field of $\mathcal X_C$ to the subfield `Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'` of $\operatorname{Frac}(\mathcal O(\Omega))$, consisting of the elements fixed by every $\gamma \in \Gamma'$ for the action of $G$ on $\mathcal O(\Omega) =$ `Omega.HolRingOf ϖ ρ` through $\rho$. The hypothesis `heval` requires $e$ to compute germs by evaluation: for every open $U$ of $\mathcal X_C$ containing the generic point $\eta$ and every section $s$ over $U$ there are $a, b \in \mathcal O(\Omega)$ with $b$ a non-zero-divisor such that the image of the germ of $s$ at $\eta$ under $e$ equals $a/b$ in $\operatorname{Frac}(\mathcal O(\Omega))$, and such that for every adic point $x$, every $z \in \Omega$ with $z = x.\mathrm{toOmega}\,C$, and every $q : \operatorname{Spec} C \to \mathcal X_C$ whose first projection is the base change of $\Phi(x)$ along $R \to C$ and whose second projection is the identity, with $q^{-1}(U) = \top$, one has $b(z) \cdot s(q) = a(z)$, the value $s(q)$ being the pullback $q^{*}s$ restricted to the whole of $\operatorname{Spec} C$ and identified with an element of $C$. The hypothesis `hfin` requires, for every such $U$ and every $n$, that the set of $z$ in the $n$-th affinoid which arise as $x.\mathrm{toOmega}\,C$ for an adic point $x$ admitting such a $q$ with $q^{-1}(U) \ne \top$ be finite.
--
--   *The semilinear datum.* Let $s$ be an isometric automorphism of $C$ over $K_0$, i.e. a ring automorphism of $C$ preserving the valuation and fixing the image of $K_0$, let $n \in \mathbb Z$, and assume `hs`: for every $y \in O^{\mathrm{nr}}$ with $\mathrm{Fr}^2 y = y$ one has $s(\psi_0(y)) = \psi_0(\mathrm{Fr}^{n} y)$ in $C$. Let $t_C : \mathcal X_C \to \mathcal X_C$ be a morphism compatible with the projections in the sense that $t_C$ followed by the projection to $\mathcal X$ is that projection (`htC₁`) and $t_C$ followed by the projection to $\operatorname{Spec} C$ is that projection followed by $\operatorname{Spec}(s)$ (`htC₂`). Let $w \in \Gamma$ satisfy $v\!\det(\sigma w) = 1$ (`hw`, `hw₁`).
--
--   *Conclusion.* For every open $U \subseteq \mathcal X_C$, every witness that the generic point $\eta$ lies in $U$, every witness that $\eta$ lies in $t_C^{-1}(U)$, and every section $\mathrm{sec}$ over $U$: the image under $e$ of the germ at $\eta$ of the pullback $t_C^{*}\mathrm{sec}$, a section over $t_C^{-1}(U)$, viewed through the inclusion of the field of $\Gamma'$-invariants into $\operatorname{Frac}(\mathcal O(\Omega))$, equals
--   $$w^{n} \cdot \mathrm{fracMap}\big(\mathtt{Omega.toAmbientOf}\ \varpi\ \rho\ s\big)\Big( e(\text{germ of } \mathrm{sec} \text{ at } \eta) \Big),$$
--   where `Omega.toAmbientOf ϖ ρ s` is the ambient semilinear automorphism with base $s$ and coefficientwise action $f \mapsto s \circ f \circ s^{-1}$ on $\mathcal O(\Omega)$, $\mathrm{fracMap}$ is its extension to $\operatorname{Frac}(\mathcal O(\Omega))$, and $w^{n}\cdot$ denotes the action of the group element $w^{n} \in G$ on $\operatorname{Frac}(\mathcal O(\Omega))$.
--
--   This is the Galois-theoretic complement to the evaluation embedding of the function field of the generic fibre of a Čerednik–Drinfeld quotient into the $\Gamma'$-invariants of the fraction field of the ring of holomorphic functions on the Drinfeld upper half plane: an isometric automorphism $s$ of the complete algebraically closed coefficient field, acting on the scheme side through $t_C$ and on $\psi_0$ through the power $\mathrm{Fr}^{n}$ of Frobenius, is transported by $e$ into the coefficientwise semilinear automorphism of $\operatorname{Frac}(\mathcal O(\Omega))$ twisted by $w^{n}$, where $w$ realises odd determinant valuation. It is used in the construction of the isomorphism between the function field of the generic fibre and the invariant field, which is the analytic description of the Shimura curve at a prime of bad reduction in the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ringHom_functionField_germ_app_eq_zpow_smul_fracMap_of_isometricAut_of_eval_of_cerednikDrinfeld_quotient.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega
  CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.ringHom_functionField_germ_app_eq_zpow_smul_fracMap_of_isometricAut_of_eval_of_cerednikDrinfeld_quotient

    {r : ℕ} [Fact r.Prime]
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
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)

    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪)) [IsProper f] [Flat f]

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (hΘnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      Θ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x))
    (hΘinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → Θ B hB x' = Θ B hB x)
    (hΘfib : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
      (∀ y : (Scheme.nilpPoints f).obj k, ∃ P : (Omega K₀ π).obj k, Θ k hk (ψ, P) = y) ∧
      ∀ P P' : (Omega K₀ π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
        ∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet k (σ γ) (ψ, P) (ψ, P'))
    (hΘuniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
      (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
        ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
          OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
          (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
          u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u B hB (Θ B hB x) = ρ' B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
            (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
            u' B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u' B hB (Θ B hB x) = ρ' B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f).obj B),
            u' B hB y = u B hB y)

    {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    [CompleteSpace C] [IsAlgClosed C]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R)
    (ψ₀ : Onr →ₐ[𝒪] R)
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : C, y ≠ 0 ∧ Valued.v y ≤ ε)
    (hex : Omega.IsExhausted ϖ) [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Φ : AdicPoint K₀ π R → {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R})
    (hΦ : (∀ (x : AdicPoint K₀ π R) (n : ℕ),
        Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ (Φ x).1 =
          (Θ (modPow π R n) (isNilpotent_algebraMap_modPow π R n)
            (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)).1) ∧
      Function.Surjective Φ ∧
      (∀ x x' : AdicPoint K₀ π R, Φ x = Φ x' ↔ ∃ γ ∈ Γ', x' = x.act (σ γ)) ∧
      (Function.Injective (fun p : {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R} =>
          Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1) ∧
        ∀ cpt : Spec (CommRingCat.of C) ⟶ 𝒳, cpt ≫ f = Scheme.specOver C →
          ∃ p : {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R},
            Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1 = cpt))

    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪))
    (hsC : sC = Spec.map (CommRingCat.ofHom ((algebraMap K₀ C).comp (algebraMap 𝒪 K₀))))
    [IsIntegral (Limits.pullback f sC)]

    (e : ↑(Limits.pullback f sC).functionField →+* ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'))
    (heval : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
        (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
        ∃ (a b : Omega.HolRingOf ϖ ρ) (hb : b ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
          ((e (((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom s) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) =
              Localization.mk a ⟨b, hb⟩ ∧
          ∀ (x : AdicPoint K₀ π R) (z : ↥(Omega.upperHalfPlane K₀ C)), (z : C) = x.toOmega C →
            ∀ (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
              q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 →
              q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) →
              ∀ (hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U),
                (show ↥(Omega.holRing ϖ) from b : ↥(Omega.upperHalfPlane K₀ C) → C) z *
                    (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
                (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqU).op).hom ((q.app U).hom s)) =
                  (show ↥(Omega.holRing ϖ) from a : ↥(Omega.upperHalfPlane K₀ C) → C) z))
    (hfin : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (n : ℕ),
        Set.Finite {z : ↥(Omega.affinoid ϖ n) | ∃ x : AdicPoint K₀ π R, (z : C) = x.toOmega C ∧
          ∃ q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC,
            q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 ∧
            q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧
            ¬ ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U)}))

    (s : Omega.IsometricAut K₀ C) (n : ℤ)
    (hs : ∀ y : Onr, Fr (Fr y) = y → s.toRingEquiv (algebraMap R C (ψ₀ y)) = algebraMap R C (ψ₀ ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) y)))
    (tC : Limits.pullback f sC ⟶ Limits.pullback f sC)
    (htC₁ : tC ≫ Limits.pullback.fst f sC = Limits.pullback.fst f sC)
    (htC₂ : tC ≫ Limits.pullback.snd f sC = Limits.pullback.snd f sC ≫ Spec.map (CommRingCat.ofHom (s.toRingEquiv : C →+* C)))
    (w : G) (hw : w ∈ Γ) (hw₁ : vdet (σ w) = Multiplicative.ofAdd (1 : ℤ)) :
    ∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
      (hU' : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ tC ⁻¹ᵁ U) (sec : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
      ((e (((Limits.pullback f sC).presheaf.germ (tC ⁻¹ᵁ U) (genericPoint (Limits.pullback f sC : Scheme.{0})) hU').hom ((tC.app U).hom sec)) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) =
        w ^ n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ s)
          ((e (((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom sec) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) := by sorry
