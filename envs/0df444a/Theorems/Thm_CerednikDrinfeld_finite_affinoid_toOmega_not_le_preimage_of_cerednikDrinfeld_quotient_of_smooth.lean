-- Prove2me | Theorems.Thm_CerednikDrinfeld_finite_affinoid_toOmega_not_le_preimage_of_cerednikDrinfeld_quotient_of_smooth
-- name    : CerednikDrinfeld.finite_affinoid_toOmega_not_le_preimage_of_cerednikDrinfeld_quotient_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/f7a5d30e-527a-5c30-a15e-b53b8226abe4
-- title:
--   Finiteness of affinoid points sent off a generic open
-- statement:
--   The data fall into several groups.
--
--   *Arithmetic base.* A prime $r$; a characteristic-zero domain $\mathcal O$ which is a discrete valuation ring (`hdvr`), an irreducible element $\pi \in \mathcal O$, with $\mathcal O$ $\pi$-adically complete (`hcomplete`), residue ring of cardinality $r$ (`hres`) and $(r) = (\pi)$ as ideals of $\mathcal O$ (`hunr`); a characteristic-zero field $K_0$ that is an $\mathcal O$-algebra and a fraction field of $\mathcal O$.
--
--   *Coefficient ring.* A characteristic-zero domain $O^{nr}$ which is an $\mathcal O$-algebra, together with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$ of $O^{nr}$, such that $O^{nr}$ is $\pi$-adically complete (`hOnr_complete`), $\pi O^{nr}$ is maximal (`hOnr_max`), every $x \in O^{nr}$ satisfies some monic polynomial over $\mathcal O$ modulo $\pi$ (`hOnr_alg`), every monic polynomial over $O^{nr}$ of positive degree has a root modulo $\pi$ (`hOnr_closed`), and $\mathrm{Fr}(x) \equiv x^{r} \pmod{\pi}$ for all $x$ (`hFr`). A monoid homomorphism $v\!\det : \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively) characterised by `hvdet`: $v\!\det(g) = n$ if and only if $\det g = u\pi^{n}$ in $K_0$ for some unit $u$ of $\mathcal O$.
--
--   *Group datum.* A group $G$, a homomorphism $\sigma : G \to \mathrm{GL}_2(K_0)$, and a subgroup $\Gamma \le G$ such that some $z \in \Gamma$ has $\sigma z$ a scalar matrix with $v\!\det(\sigma z) = 2$ (`hcent`) and some $w \in \Gamma$ has $v\!\det(\sigma w) = 1$ (`hodd`); a subgroup $\Gamma'$ whose members are exactly the $x \in \Gamma$ with $v\!\det(\sigma x)$ even (`hΓ'`). A homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ with $\rho g$ the class of $\sigma g$ (`hρ`), such that for every vertex $v$ of the lattice tree over $(\mathcal O, K_0)$ — a homothety class of full lattices in $K_0^2$ — the stabiliser of $v$ in $\rho(\Gamma')$ is finite (`hdisc`), and some finite set of vertices meets every $\rho(\Gamma')$-orbit (`hcocpt`).
--
--   *The scheme.* A scheme $\mathcal X$ and a proper flat morphism $f : \mathcal X \to \operatorname{Spec}\mathcal O$, with `hsmooth`: the second projection of the fibre product of $f$ with $\operatorname{Spec}(K_0) \to \operatorname{Spec}(\mathcal O)$ is smooth of relative dimension $1$, i.e. the generic fibre is a smooth curve over $K_0$.
--
--   *The uniformising transformation $\Theta$.* For every commutative $\mathcal O$-algebra $B$ in which $\pi$ is nilpotent, a map
--   $$\Theta_B : \mathrm{Hom}_{\mathcal O\text{-alg}}(O^{nr}, B) \times \mathrm{DeligneDatum}(\pi, B) \longrightarrow \{\varphi : \operatorname{Spec} B \to \mathcal X \mid f \circ \varphi = \operatorname{Spec}(\mathcal O \to B)\},$$
--   where a Deligne datum over $B$ assigns to each full lattice $M \subset K_0^2$ a $B$-submodule $\mathrm{line}(M)$ of $B \otimes_{\mathcal O} M$ with invertible quotient, monotone under inclusions of lattices, equivariant for scalar homotheties, and non-degenerate at every prime of $B$. Four hypotheses are imposed: `hΘnat`, naturality of $\Theta$ in $B$ along $\mathcal O$-algebra maps; `hΘinv`, invariance $\Theta_B(x') = \Theta_B(x)$ whenever $\gamma \in \Gamma$ and $x, x'$ satisfy `OmegaNr.IsTwistedAct` for $\sigma\gamma$, that is, the $O^{nr}$-component of $x'$ is the $O^{nr}$-component of $x$ precomposed with $\mathrm{Fr}^{-v\!\det(\sigma\gamma)}$ and the Deligne datum of $x'$ is the pullback of that of $x$ along $(\sigma\gamma)^{-1}$; `hΘfib`, for every algebraically closed field $k$ which is an $\mathcal O$-algebra with $\pi$ nilpotent and every $\mathcal O$-algebra map $\psi : O^{nr} \to k$, the map $P \mapsto \Theta_k(\psi, P)$ is onto the $k$-points of $f$ and $\Theta_k(\psi,P) = \Theta_k(\psi,P')$ holds precisely when $(\psi,P)$ and $(\psi,P')$ are related by `OmegaNr.IsTwistedAct` for some $\sigma\gamma$ with $\gamma \in \Gamma$; and `hΘuniv`, the universal property: for every scheme $T$ over $\operatorname{Spec}\mathcal O$ and every natural, $\Gamma$-invariant family $\rho'$ of maps from the same functor into the nilpotent points of $T$, there is a natural family $u$ of maps from the nilpotent points of $f$ to those of $T$ with $u \circ \Theta = \rho'$, and any natural family $u'$ with $u' \circ \Theta = \rho'$ agrees with $u$.
--
--   *Analytic frame.* A field $C$ which is a $K_0$-algebra, carrying a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed; a commutative ring $R$ which is an $\mathcal O$-algebra with $C$ an $R$-algebra, compatibly with the towers $\mathcal O \to R \to C$ and $\mathcal O \to K_0 \to C$; a pseudo-uniformiser $\varpi$, namely an element of $K_0$ whose image in $C$ has valuation strictly between $0$ and $1$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N$. The hypothesis `hF` asserts that $(\pi, \varpi, R)$ is an adic frame: $\pi$ is irreducible, $R \to C$ is injective with image exactly $\{c : v(c) \le 1\}$, $R$ is $\pi$-adically complete, $\{a \in K_0 : v(a) \le 1\}$ is the image of $\mathcal O$, the image of $K_0$ in $C$ is closed, and $\pi$ and $\varpi$ have the same image in $C$. Further: an $\mathcal O$-algebra map $\psi_0 : O^{nr} \to R$; `hrk`, for $x, y \in C$ with $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$; `hval`, every nonzero $\varepsilon \in \Gamma_0$ satisfies $v(y) \le \varepsilon$ for some $y \ne 0$; `hex`, every $z \in C \setminus K_0$ lies in the affinoid $\mathrm{affinoid}(\varpi, n)$ for some $n$, where $\mathrm{affinoid}(\varpi,n)$ is the set of $z \in C$ with $v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^{n}$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$; and the assumption that `Omega.HolRingOf ϖ ρ`, the ring of functions on $C \setminus K_0$ that are holomorphic on each such affinoid, is a domain.
--
--   *Uniformisation of adic points.* A map $\Phi$ from `AdicPoint K₀ π R` — compatible systems of Deligne data $x.\mathrm{pt}(n)$ over $R/(\pi^{n+1})$ — to the set of morphisms $p : \operatorname{Spec} R \to \mathcal X$ with $f \circ p$ the structure morphism, subject to the four-part hypothesis `hΦ`: (i) for every $x$ and $n$, the reduction $\operatorname{Spec}(R/(\pi^{n+1})) \to \operatorname{Spec} R$ followed by $\Phi x$ equals $\Theta_{R/(\pi^{n+1})}$ applied to the pair consisting of $\psi_0$ followed by the quotient map and $x.\mathrm{pt}(n)$; (ii) $\Phi$ is surjective; (iii) $\Phi x = \Phi x'$ if and only if $x' = x.\mathrm{act}(\sigma\gamma)$ for some $\gamma \in \Gamma'$; (iv) composition with $\operatorname{Spec}(R \to C) : \operatorname{Spec} C \to \operatorname{Spec} R$ is injective on such $R$-points and every $C$-point of $f$ is obtained in this way.
--
--   *Base change to $C$.* A morphism $s_C : \operatorname{Spec} C \to \operatorname{Spec}\mathcal O$ equal to $\operatorname{Spec}$ of the composite $\mathcal O \to K_0 \to C$ (`hsC`), with the fibre product $\mathcal X_C := \mathcal X \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec} C$ integral; a ring isomorphism $e$ from the function field of $\mathcal X_C$ onto the subfield of $\mathrm{Frac}(\mathrm{HolRingOf}(\varpi,\rho))$ of elements fixed by every $\gamma \in \Gamma'$, which is $C$-linear in the sense of `he₀`: for every $c \in C$, $e$ of the image of $c$ under [`AlgebraicCurve.baseToFunctionField`](def/AlgebraicCurve_CurveModel.html#L18) of the second projection is the image of $c$ under the structural map into that invariant field.
--
--   *Conclusion.* For every open subset $U$ of $\mathcal X_C$ containing the generic point of $\mathcal X_C$, and every $n \in \mathbb N$, the following subset of $\mathrm{affinoid}(\varpi, n)$ is finite: the set of $z$ for which there exists an adic point $x$ with $z = x.\mathrm{toOmega}\,C$ — the unique element $z$ of $C$ with $(z,1) \in x.\mathrm{lineC}\,C$, the $C$-span in $C^2$ of the image of the submodule `x.stdLine`, and $0$ when no such unique element exists — and a morphism $q : \operatorname{Spec} C \to \mathcal X_C$ such that $q$ followed by the first projection equals $\operatorname{Spec}(R \to C)$ followed by $\Phi x$, $q$ followed by the second projection is the identity of $\operatorname{Spec} C$, and the preimage $q^{-1}(U)$ is not the whole of $\operatorname{Spec} C$.
--
--   A local-finiteness statement in the Čerednik–Drinfeld uniformisation of the curve $\mathcal X_C$: inside each affinoid of the Drinfeld upper half-plane $C \setminus K_0$, only finitely many coordinates come from adic points whose associated $C$-point of $\mathcal X_C$ fails to lie in a prescribed open neighbourhood of the generic point. Relative to the version without `hsmooth`, this edition carries the extra assumption that the generic fibre is a smooth curve over $K_0$; it feeds the identification of the function field of $\mathcal X_C$ with the $\Gamma'$-invariants of the fraction field of the ring of holomorphic functions, in [`CerednikDrinfeld.exists_ringEquiv_functionField_pullback_invariantFieldOf_smul_level_of_cerednikDrinfeld_quotient_of_tame_of_virtuallyTorsionFree_of_smooth`](thm.html#CerednikDrinfeld.exists_ringEquiv_functionField_pullback_invariantFieldOf_smul_level_of_cerednikDrinfeld_quotient_of_tame_of_virtuallyTorsionFree_of_smooth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_finite_affinoid_toOmega_not_le_preimage_of_cerednikDrinfeld_quotient_of_smooth.lean

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

theorem CerednikDrinfeld.finite_affinoid_toOmega_not_le_preimage_of_cerednikDrinfeld_quotient_of_smooth

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

    (hsmooth : SmoothOfRelativeDimension 1 (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K₀)))))

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
    (e : ↑(Limits.pullback f sC).functionField ≃+* ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'))
    (he₀ : (∀ c : C, e (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f sC) c) =
        algebraMap C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') c)) :
    (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (n : ℕ),
      Set.Finite {z : ↥(Omega.affinoid ϖ n) | ∃ x : AdicPoint K₀ π R, (z : C) = x.toOmega C ∧
        ∃ q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC,
          q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 ∧
          q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧
          ¬ ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U)}) := by sorry
