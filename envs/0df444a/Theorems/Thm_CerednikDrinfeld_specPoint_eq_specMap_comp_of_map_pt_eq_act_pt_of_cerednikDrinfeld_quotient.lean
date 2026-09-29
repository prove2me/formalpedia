-- Prove2me | Theorems.Thm_CerednikDrinfeld_specPoint_eq_specMap_comp_of_map_pt_eq_act_pt_of_cerednikDrinfeld_quotient
-- name    : CerednikDrinfeld.specPoint_eq_specMap_comp_of_map_pt_eq_act_pt_of_cerednikDrinfeld_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/153b3bc3-5b14-5055-989b-25b7ff9830fb
-- title:
--   Twisting a Čerednik–Drinfeld adic point by a base automorphism
-- statement:
--   Fix a prime $r$ and a complete discrete valuation ring $\mathcal O$ of characteristic zero with uniformiser $\pi$, residue field of cardinality $r$ and $(r)=(\pi)$, with fraction field $K_0$. Let $O^{\mathrm{nr}}$ be a characteristic-zero domain over $\mathcal O$, $(\pi)$-adically complete, with $(\pi)$ maximal, every element satisfying a monic $\mathcal O$-polynomial modulo $\pi$, every monic polynomial of positive degree having a root modulo $\pi$, and $\mathrm{Fr}$ an $\mathcal O$-algebra automorphism with $\mathrm{Fr}(x)\equiv x^{r}$ modulo $\pi$. Let $v\det:\mathrm{GL}_2(K_0)\to\mathbb Z$ satisfy $v\det(g)=n$ exactly when $\det g=u\pi^{n}$ for a unit $u$ of $\mathcal O$. Let $G$ be a group, $\sigma:G\to\mathrm{GL}_2(K_0)$, $\Gamma\le G$ containing a scalar element of $v\det$-value $2$ and an element of value $1$, $\Gamma'$ the elements of $\Gamma$ of even $v\det$-value, $\rho$ the induced map to $\mathrm{PGL}_2(K_0)$, the image of $\Gamma'$ acting on the vertices of the lattice tree with finite stabilisers and finitely many orbits. Let $f:\mathcal X\to\operatorname{Spec}\mathcal O$ be proper and flat, and let $\Theta$ assign, to each $\mathcal O$-algebra $B$ with $\pi$ nilpotent, a map from pairs consisting of an $\mathcal O$-algebra homomorphism $O^{\mathrm{nr}}\to B$ and a Deligne datum over $B$ to the $B$-points of $f$ (morphisms $\operatorname{Spec}B\to\mathcal X$ over $\operatorname{Spec}\mathcal O$), subject to: naturality in $B$; invariance under the twisted $\Gamma$-action, where $(\psi,P)$ and $(\psi',P')$ are related by $g$ when $\psi'$ is the $\mathrm{Fr}$-twist of $\psi$ by $-v\det(g)$ and $P'$ is the pullback of $P$ along $g^{-1}$; over algebraically closed fields $k$ with $\pi$ nilpotent and fixed $\psi$, surjectivity onto $k$-points and fibres exactly the twisted $\Gamma$-orbits; and the universal property of an initial such natural twisted-invariant transformation. Let $R$ be a local $(\pi)$-adically complete $\mathcal O$-algebra, $\psi_0:O^{\mathrm{nr}}\to R$, $\tau$ an $\mathcal O$-algebra automorphism of $R$ and $n\in\mathbb Z$ with $\tau\circ\psi_0=\psi_0\circ\mathrm{Fr}^{n}$ on elements fixed by $\mathrm{Fr}^{2}$, and $\tau_k$ the induced endomorphisms of $R/(\pi^{k+1})$. Let $w\in\Gamma$ have $v\det(\sigma w)=1$. Let $PX$ send each adic point $x$ — a compatible system of Deligne data over the rings $R/(\pi^{k+1})$ — to a morphism $\operatorname{Spec}R\to\mathcal X$ whose restriction modulo $\pi^{k+1}$ is the morphism underlying $\Theta(\psi_0 \bmod \pi^{k+1}, x_k)$. Then for adic points $x,x'$ such that the base change of $x'_k$ along $\tau_k$ equals the $\sigma(w^{-n})$-translate of $x$ at level $k$ for all $k$, one has $PX\,x=\operatorname{Spec}(\tau)$ followed by $PX\,x'$.
--
--   This is the compatibility of the Čerednik–Drinfeld uniformisation of a quotient curve with a base automorphism: twisting the adic point by an automorphism $\tau$ of the complete local ring, whose effect on the unramified coefficients is a power of Frobenius, changes the resulting $R$-point only by composition with $\operatorname{Spec}(\tau)$, once the adic data are matched by a $\Gamma$-translation. It is used in the computation of the action of an isometric automorphism on germs of functions on the uniformised curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_specPoint_eq_specMap_comp_of_map_pt_eq_act_pt_of_cerednikDrinfeld_quotient.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve
open CerednikDrinfeld

theorem CerednikDrinfeld.specPoint_eq_specMap_comp_of_map_pt_eq_act_pt_of_cerednikDrinfeld_quotient

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

    {R : Type} [CommRing R] [Algebra 𝒪 R] [IsLocalRing R] (hR : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (ψ₀ : Onr →ₐ[𝒪] R)

    (τ : R ≃ₐ[𝒪] R) (n : ℤ) (hψτ : ∀ y : Onr, Fr (Fr y) = y → τ (ψ₀ y) = ψ₀ ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) y))
    (τn : ∀ k : ℕ, modPow π R k →ₐ[𝒪] modPow π R k)
    (hτn : ∀ (k : ℕ) (a : R), τn k (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) a) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) (τ a))

    (w : G) (hw : w ∈ Γ) (hw₁ : vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))

    (PX : AdicPoint K₀ π R → (Spec (CommRingCat.of R) ⟶ 𝒳))
    (hPX : ∀ (x : AdicPoint K₀ π R) (k : ℕ),
      Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R k))) ≫ PX x =
        (Θ (modPow π R k) (isNilpotent_algebraMap_modPow π R k)
          (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)})).comp ψ₀), x.pt k)).1)
    (x x' : AdicPoint K₀ π R) (hx' : ∀ k : ℕ, DeligneDatum.map π (τn k) (x'.pt k) = (x.act (σ (w ^ (-n)))).pt k) :
    PX x = Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) ≫ PX x' := by sorry
