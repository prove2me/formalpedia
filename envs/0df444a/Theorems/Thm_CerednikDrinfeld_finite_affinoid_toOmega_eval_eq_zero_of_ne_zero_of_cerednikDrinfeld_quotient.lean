-- Prove2me | Theorems.Thm_CerednikDrinfeld_finite_affinoid_toOmega_eval_eq_zero_of_ne_zero_of_cerednikDrinfeld_quotient
-- name    : CerednikDrinfeld.finite_affinoid_toOmega_eval_eq_zero_of_ne_zero_of_cerednikDrinfeld_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/fd9a7d36-512f-56eb-a91c-0a760116b802
-- title:
--   Finitely many affinoid coordinates where a non-zero section vanishes
-- statement:
--   The setting is a Čerednik–Drinfeld quotient datum together with an analytic frame, organised as follows.
--
--   *Base.* A prime $r$; a characteristic-zero domain $\mathcal{O}$ which is a discrete valuation ring (`hdvr`), an irreducible element $\pi \in \mathcal{O}$ (`hπ`), completeness of $\mathcal{O}$ for the $\pi$-adic topology (`hcomplete`), residue ring $\mathcal{O}/(\pi)$ of cardinality $r$ (`hres`) and $(r) = (\pi)$ in $\mathcal{O}$ (`hunr`); a characteristic-zero field $K_0$ which is a fraction field of $\mathcal{O}$.
--
--   *Unramified coefficients.* A characteristic-zero domain $O^{\mathrm{nr}}$ which is an $\mathcal{O}$-algebra, an $\mathcal{O}$-algebra automorphism $\mathrm{Fr}$ of it, and the hypotheses that $O^{\mathrm{nr}}$ is $\pi$-adically complete (`hOnr_complete`), that $(\pi)$ is maximal in $O^{\mathrm{nr}}$ (`hOnr_max`), that every element of $O^{\mathrm{nr}}$ satisfies a monic polynomial over $\mathcal{O}$ modulo $\pi$ (`hOnr_alg`), that every monic polynomial over $O^{\mathrm{nr}}$ of positive degree has a root modulo $\pi$ (`hOnr_closed`), and that $\mathrm{Fr}(x) \equiv x^{r} \pmod{\pi}$ for all $x$ (`hFr`).
--
--   *Determinant valuation.* A homomorphism $v\!\det : \mathrm{GL}_2(K_0) \to \mathbb{Z}$ (written multiplicatively) such that $v\!\det(g) = n$ if and only if $\det g = u\pi^{n}$ for some unit $u$ of $\mathcal{O}$ (`hvdet`).
--
--   *Arithmetic group.* A group $G$, a homomorphism $\sigma : G \to \mathrm{GL}_2(K_0)$ and a subgroup $\Gamma \le G$; the hypothesis `hcent` provides $z \in \Gamma$ with $\sigma z$ a scalar matrix and $v\!\det(\sigma z) = 2$, and `hodd` provides $w \in \Gamma$ with $v\!\det(\sigma w) = 1$; $\Gamma'$ is a subgroup characterised by `hΓ'` as the set of $x \in \Gamma$ with $v\!\det(\sigma x)$ even. A homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ is the projectivisation of $\sigma$ (`hρ`); the image $\rho(\Gamma')$ has finite stabiliser of every vertex of the Bruhat–Tits tree of $\mathcal{O} \subset K_0$ (`hdisc`) and finitely many vertices meet every $\rho(\Gamma')$-orbit (`hcocpt`).
--
--   *The quotient.* A scheme $\mathcal{X}$ with a proper flat morphism $f : \mathcal{X} \to \operatorname{Spec}\mathcal{O}$, together with a family $\Theta$ which, for every $\mathcal{O}$-algebra $B$ in which $\pi$ is nilpotent, maps pairs $(\psi, P)$ consisting of an $\mathcal{O}$-algebra map $\psi : O^{\mathrm{nr}} \to B$ and a Deligne datum $P$ over $B$ for $\pi$ (a family of $B$-submodules $P(M) \subseteq B \otimes_{\mathcal{O}} M$, indexed by the full lattices $M \subset K_0^2$, with invertible quotients, compatible with inclusions, equivariant for scalar homotheties, and non-degenerate at every prime of $B$) to points $\varphi : \operatorname{Spec} B \to \mathcal{X}$ with $\varphi$ followed by $f$ equal to $\operatorname{Spec}(\mathcal{O}\to B)$. The hypotheses on $\Theta$ are: naturality in $B$ (`hΘnat`); invariance under the twisted action of $\Gamma$, where $\mathrm{IsTwistedAct}$ for $g \in \mathrm{GL}_2(K_0)$ relates $(\psi,P)$ to $(\psi \circ \mathrm{Fr}^{-v\!\det(g)}, g^{-1}\text{-pullback of }P)$ (`hΘinv`); over every algebraically closed field $k$ which is an $\mathcal{O}$-algebra with $\pi$ nilpotent and every $\psi : O^{\mathrm{nr}} \to k$, surjectivity of $P \mapsto \Theta_k(\psi, P)$ onto such $k$-points and the identification of its fibres with the orbits of the twisted $\Gamma$-action (`hΘfib`); and the universal property `hΘuniv`, asserting that for every scheme $T$ over $\operatorname{Spec}\mathcal{O}$ and every natural, twist-invariant family $\rho'$ into the $\pi$-nilpotent points of $T$ there is a unique natural family $u$ from the $\pi$-nilpotent points of $f$ to those of $T$ with $u \circ \Theta = \rho'$.
--
--   *Analytic frame.* A complete algebraically closed field $C$ with a $\Gamma_0$-valued valuation, a $K_0$-algebra; a commutative ring $R$ which is an $\mathcal{O}$-algebra with $C$ an $R$-algebra, the scalar towers $\mathcal{O} \subset R \subset C$ and $\mathcal{O} \subset K_0 \subset C$ being assumed; a pseudo-uniformiser $\varpi$, that is an element $\varpi.\varpi \in K_0$ whose image in $C$ has valuation strictly between $0$ and $1$ and whose powers bound the valuation of every non-zero element of $K_0$ from both sides; and the frame hypothesis `hF`, which requires $\pi$ irreducible, $R \to C$ injective with image exactly the closed unit ball of $C$, $R$ $\pi$-adically complete, $\mathcal{O}$ the unit ball of $K_0$, the image of $K_0$ closed in $C$, and $\pi$ and $\varpi.\varpi$ having the same image in $C$. Further: an $\mathcal{O}$-algebra map $\psi_0 : O^{\mathrm{nr}} \to R$; the archimedean property `hrk` (for $x$ with $v(x) < 1$ and $y \neq 0$ some power $v(x)^n \le v(y)$); the cofinality `hval` (every non-zero $\varepsilon \in \Gamma_0$ dominates the valuation of some non-zero element of $C$); the hypothesis `hex` that the affinoids $\mathrm{affinoid}\,\varpi\,n = \{z \in C : v(z) \le v(\varpi)^{-n} \text{ and } v(z - a) \ge v(\varpi)^{n} \text{ for all } a \in K_0 \text{ with } v(a) \le v(\varpi)^{-n}\}$ exhaust the Drinfeld upper half plane $C \setminus K_0$; and that the ring of functions on $C\setminus K_0$ holomorphic on each affinoid is a domain.
--
--   *Uniformisation of adic points.* A map $\Phi$ sending each adic point $x$ (a compatible system of Deligne data over the quotients $R/(\pi^{n+1})$) to an $R$-point of $\mathcal{X}$ over $\operatorname{Spec} R$, subject to the four clauses of `hΦ`: the reduction of $\Phi(x)$ modulo $\pi^{n+1}$ is $\Theta$ applied to the pair consisting of $\psi_0$ reduced modulo $\pi^{n+1}$ and the $n$-th layer $x.\mathrm{pt}\,n$; $\Phi$ is surjective; $\Phi(x) = \Phi(x')$ if and only if $x' = x.\mathrm{act}(\sigma\gamma)$ for some $\gamma \in \Gamma'$; and base change along $R \to C$ is injective on such $R$-points and hits every $C$-point of $\mathcal{X}$ over $\operatorname{Spec}\mathcal{O}$.
--
--   *Base change to $C$.* A morphism $s_C : \operatorname{Spec} C \to \operatorname{Spec}\mathcal{O}$ equal to the one induced by $\mathcal{O} \to K_0 \to C$ (`hsC`), with the pullback $\mathcal{X}_C := \mathcal{X} \times_{\operatorname{Spec}\mathcal{O}} \operatorname{Spec} C$ integral. Finally, the hypothesis `hfin`: for every open $U$ of $\mathcal{X}_C$ containing the generic point of $\mathcal{X}_C$ and every $n \in \mathbb{N}$, only finitely many $z \in \mathrm{affinoid}\,\varpi\,n$ are of the form $z = x.\mathrm{toOmega}\,C$ for an adic point $x$ admitting a morphism $q : \operatorname{Spec} C \to \mathcal{X}_C$ whose composite with the first projection is the base change of $\Phi(x)$ along $R \to C$, whose composite with the second projection is the identity, and for which $\top \not\le q^{-1}U$. Here $x.\mathrm{toOmega}\,C$ denotes the unique $z \in C$ with $(z,1)$ in the $C$-line attached to $x$, when such a $z$ exists uniquely, and $0$ otherwise.
--
--   *Conclusion.* For every open $V$ of $\mathcal{X}$, every open $W$ of $\mathcal{X}_C$ with $W \le \mathrm{pr}_1^{-1}V$ (`hWV`) and containing the generic point of $\mathcal{X}_C$ (`hWη`), every $m' \in \mathbb{N}$ and all families $\mathrm{den} : \mathrm{Fin}\,m' \to \Gamma(V, \mathcal{O}_{\mathcal{X}})$ and $\mathrm{cden} : \mathrm{Fin}\,m' \to C$, consider the section
--   $$D \;=\; \sum_{j} \big(\mathrm{cden}_j \text{ viewed as a global section of } \operatorname{Spec} C, \text{ pulled back along } \mathrm{pr}_2 \text{ and restricted to } W\big)\cdot\big(\mathrm{den}_j \text{ pulled back along } \mathrm{pr}_1 \text{ and restricted to } W\big) \;\in\; \Gamma(W, \mathcal{O}_{\mathcal{X}_C}).$$
--   If $D \neq 0$, then for every $n \in \mathbb{N}$ the following subset of $\mathrm{affinoid}\,\varpi\,n$ is finite: the set of those $z$ for which there exist an adic point $x$ with $z = x.\mathrm{toOmega}\,C$ and a morphism $q : \operatorname{Spec} C \to \mathcal{X}_C$ such that $q$ followed by the first projection equals the base change of $\Phi(x)$ along $R \to C$, $q$ followed by the second projection is the identity of $\operatorname{Spec} C$, the preimage $q^{-1}W$ is all of $\operatorname{Spec} C$, and the value of $D$ at $q$ — the image of $D$ under $q^{*}$ on $W$, restricted to the whole of $\operatorname{Spec} C$ and transported along the isomorphism $\Gamma(\operatorname{Spec} C, \mathcal{O}) \cong C$ — is zero.
--
--   This is a finiteness step in the comparison between the Čerednik–Drinfeld rigid-analytic uniformisation and the scheme $\mathcal{X}_C$: a non-zero $C$-linear combination of pulled-back sections of $\mathcal{X}$ over an open neighbourhood of the generic point of $\mathcal{X}_C$ vanishes at only finitely many coordinates of each affinoid, so that clearing denominators affects only finitely many points. It is used in the construction of holomorphic representatives on edge regions after denominator clearing, on the way to embedding the function field of $\mathcal{X}_C$ into the ring of functions holomorphic on every affinoid.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_finite_affinoid_toOmega_eval_eq_zero_of_ne_zero_of_cerednikDrinfeld_quotient.lean

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

theorem CerednikDrinfeld.finite_affinoid_toOmega_eval_eq_zero_of_ne_zero_of_cerednikDrinfeld_quotient

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

    (hfin : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (n : ℕ),
        Set.Finite {z : ↥(Omega.affinoid ϖ n) | ∃ x : AdicPoint K₀ π R, (z : C) = x.toOmega C ∧
          ∃ q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC,
            q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 ∧
            q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧
            ¬ ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U)})) :
    ∀ (V : 𝒳.Opens) (W : (Limits.pullback f sC).Opens) (hWV : W ≤ (Limits.pullback.fst f sC) ⁻¹ᵁ V)
      (hWη : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ W)
      (m' : ℕ) (den : Fin m' → 𝒳.presheaf.obj (Opposite.op V)) (cden : Fin m' → C),
      (∑ j, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cden j))) *
              ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (den j))) ≠ 0 →
      ∀ n : ℕ, Set.Finite {z : ↥(Omega.affinoid ϖ n) | ∃ x : AdicPoint K₀ π R, (z : C) = x.toOmega C ∧
          ∃ (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
            q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 ∧
            q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧
            ∃ (hqW : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ W),
              (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
                (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqW).op).hom ((q.app W).hom
                  (∑ j, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cden j))) *
              ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (den j))))) = 0} := by sorry
