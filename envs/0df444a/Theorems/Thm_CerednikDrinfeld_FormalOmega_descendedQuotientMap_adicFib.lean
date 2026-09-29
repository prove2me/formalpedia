-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_descendedQuotientMap_adicFib
-- name    : CerednikDrinfeld.FormalOmega.descendedQuotientMap_adicFib
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/833711bd-7ebf-588b-aa47-ff7376d799fd
-- title:
--   Adic points and fibres of the descended quotient map
-- statement:
--   The setting is the following. Fix a prime $r$ and a characteristic-zero domain $\mathcal O$ which is a discrete valuation ring, together with an irreducible element $\pi \in \mathcal O$; it is assumed that $\mathcal O$ is $\pi$-adically complete (`hcomplete`), that $\#(\mathcal O/\pi) = r$ (`hres`) and that $(r) = (\pi)$ as ideals of $\mathcal O$ (`hunr`), and $K_0$ is a characteristic-zero field which is a fraction field of $\mathcal O$.
--
--   Next, $Onr$ is a characteristic-zero $\mathcal O$-algebra which is a domain, equipped with an $\mathcal O$-algebra automorphism $Fr$, subject to: $\pi$-adic completeness of $Onr$ (`hOnr_complete`); maximality of the ideal $(\pi Onr)$ (`hOnr_max`); the condition `hOnr_alg` that every $x \in Onr$ satisfies some monic polynomial over $\mathcal O$ with value in $\pi Onr$; the condition `hOnr_closed` that every monic polynomial over $Onr$ of positive degree has a root modulo $\pi$; and the congruence `hFr`, $Fr(x) \equiv x^{r} \pmod{\pi Onr}$ for all $x$. Thus $Onr$ plays the role of the completion of the maximal unramified extension of $\mathcal O$ with its Frobenius. A homomorphism $vdet : \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively) is given, characterised by `hvdet`: $vdet(g) = n$ if and only if $\det g = u\,\pi^{n}$ in $K_0$ for some unit $u$ of $\mathcal O$.
--
--   The group data consist of a group $G$, a homomorphism $\sigma : G \to \mathrm{GL}_2(K_0)$, a subgroup $\Gamma \le G$, and: `hcent`, some $z \in \Gamma$ with $\sigma z$ a scalar matrix and $vdet(\sigma z) = 2$; `hodd`, some $w \in \Gamma$ with $vdet(\sigma w) = 1$; a subgroup $\Gamma'$ characterised by `hΓ'` as the set of $x \in \Gamma$ with $vdet(\sigma x)$ even. Further, $\rho : G \to \mathrm{PGL}_2(K_0)$ is the projectivisation of $\sigma$ (`hρ`), the image $\rho(\Gamma')$ has finite stabilisers on the vertices of the tree (homothety classes of full lattices in $K_0^2$) by `hdisc`, and finitely many vertices meet every $\rho(\Gamma')$-orbit by `hcocpt`. The matrix $g_1$ is the diagonal matrix with entries $\pi, 1$ (`hg₁`). Finally $N \le \mathrm{PGL}_2(K_0)$ satisfies $N \le \rho(\Gamma')$ (`hNle`), $N$ is normal when regarded inside $\rho(\Gamma)$ (`hNnorm`), and $N$ has nonzero relative index in $\rho(\Gamma')$ (`hNidx`); and $DM$ is a `MumfordTower` for $(\mathcal O, \pi, K_0, r, g_1, N)$, that is, a tower of schemes $DM.Z_n$ over $\mathrm{Spec}(\mathcal O/\pi^{n+1})$ with proper flat structure maps $DM.zb_n$, cartesian transitions $DM.zt_n$, affine neighbourhoods of finite sets, and a point map $DM.q$ sending a Deligne datum over an $\mathcal O$-algebra $B$ killed by $\pi^{n+1}$ to a morphism $\mathrm{Spec}\,B \to DM.Z_n$, natural, compatible with the transitions, invariant under $N$, and given on charts by open immersions.
--
--   The twisted tower is the following data. Schemes $X_n$ with morphisms $xb_n : X_n \to \mathrm{Spec}(\mathcal O/\pi^{n+1})$ and transitions $xt_n : X_n \to X_{n+1}$, a finite group $G_2$ acting by $a_n : G_2 \to \mathrm{Aut}(X_n)$, projections $pr_{1,n} : X_n \to DM.Z_n$ and $pr_{2,n} : X_n \to \mathrm{Spec}(\mathcal O_2/\pi^{n+1})$, where $\mathcal O_2$ denotes the subalgebra `AlgHom.equalizer` of $Onr$ on which $Fr^2$ agrees with the identity, a homomorphism $\theta : \Gamma \to G_2$, and $\mathcal O$-algebra automorphisms $Fr_{2,n}$ of $\mathcal O_2/\pi^{n+1}$. The hypotheses on these data are: `hcart`, each square $(xt_n, xb_n, xb_{n+1}, \mathrm{Spec}$ of the quotient map $\mathcal O/\pi^{n+2} \to \mathcal O/\pi^{n+1})$ is a pullback; `hproper` and `hflat`, each $xb_n$ is proper and flat; `haff`, every finite subset of $X_n$ lies in an affine open; `ha_over` and `ha_xt`, the $G_2$-action is over the base and commutes with the transitions; `hX`, $X_n$ is the fibre product of $DM.Z_n$ and $\mathrm{Spec}(\mathcal O_2/\pi^{n+1})$ over $\mathrm{Spec}(\mathcal O/\pi^{n+1})$ via $pr_{1,n}$ and $pr_{2,n}$; `hxb`, $xb_n$ is $pr_{1,n}$ followed by $DM.zb_n$; `hxt₁` and `hxt₂`, the projections are compatible with the transitions on both factors; `hθsurj`, $\theta$ is surjective, and `hθker`, $\theta\gamma = 1$ if and only if $\rho\gamma \in N$; `hFr₂`, $Fr_{2,n}$ is induced by $Fr$ on $\mathcal O_2/\pi^{n+1}$; `ha_pr₂`, for $\gamma \in \Gamma$ the automorphism $a_n(\theta\gamma)$ followed by $pr_{2,n}$ equals $pr_{2,n}$ followed by $\mathrm{Spec}$ of $Fr_{2,n}^{-vdet(\sigma\gamma)}$; and `ha_pr₁`, for $\gamma \in \Gamma$, an $\mathcal O$-algebra $B$ with $\pi^{n+1} = 0$ in $B$ and Deligne data $P, P'$ over $B$ with $P'$ the pullback of $P$ along $(\sigma\gamma)^{-1}$, any $x : \mathrm{Spec}\,B \to X_n$ with $x$ followed by $pr_{1,n}$ equal to $DM.q_n(P)$ satisfies that $x$ followed by $a_n(\theta\gamma)$ and then $pr_{1,n}$ equals $DM.q_n(P')$.
--
--   Finally, $DQ$ is a `TowerQuotientDatum` for $(\mathcal O, \pi, X, xb, xt, G_2, a)$: a tower $DQ.Y_n$ over $\mathrm{Spec}(\mathcal O/\pi^{n+1})$ with proper flat structure maps $DQ.yb_n$ and cartesian transitions $DQ.yt_n$, together with $G_2$-invariant finite surjective morphisms $DQ.p_n : X_n \to DQ.Y_n$ over the base, compatible with the transitions and cartesian over them, locally epimorphic, and universal among $G_2$-invariant morphisms out of the $X_n$. The point map of the quotient tower is a family $q$ assigning, to each $n$, each $\mathcal O$-algebra $B$ with $\pi^{n+1} = 0$ in $B$, and each pair consisting of an $\mathcal O$-algebra map $Onr \to B$ and a Deligne datum over $B$, a morphism $\mathrm{Spec}\,B \to DQ.Y_n$; the hypothesis `hqdef` pins $q$ down: whenever $\psi : Onr \to B$ is an $\mathcal O$-algebra map, $\psi_2 : \mathcal O_2/\pi^{n+1} \to B$ is the induced map (so $\psi_2$ of the class of $y$ is $\psi(y)$), $P$ is a Deligne datum over $B$, and $x : \mathrm{Spec}\,B \to X_n$ satisfies $x$ followed by $pr_{1,n}$ equal to $DM.q_n(P)$ and $x$ followed by $pr_{2,n}$ equal to $\mathrm{Spec}\,\psi_2$, then $q_n(\psi, P) = x$ followed by $DQ.p_n$.
--
--   Under these hypotheses the assertion is the following, for every algebraically closed field $C$ that is a $K_0$-algebra, carrying a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$ and complete for it, every commutative $\mathcal O$-algebra $R$ with compatible maps into $C$ (forming scalar towers $\mathcal O \to R \to C$ and $\mathcal O \to K_0 \to C$), every pseudo-uniformizer $\varpi$ of $K_0$ in $C$, under the hypothesis that $(\pi, \varpi, R)$ is an adic frame — that is, $\pi$ is irreducible, $R \to C$ is injective with image the elements of valuation at most $1$, $R$ is $\pi$-adically complete, the elements of $K_0$ of valuation at most $1$ are exactly those coming from $\mathcal O$, the image of $K_0$ in $C$ is closed, and $\pi$ maps to $\varpi$ — every $\mathcal O$-algebra map $\psi_0 : Onr \to R$, and the hypothesis `hmod` that $\pi^{n+1} = 0$ in $R/\pi^{n+1}R$ for all $n$. Writing $\psi_{0,n}$ for the composite of $\psi_0$ with the reduction $R \to R/\pi^{n+1}R$, the conclusion is the conjunction of two statements.
--
--   First, lifting: for every family of morphisms $\eta_n : \mathrm{Spec}(R/\pi^{n+1}R) \to DQ.Y_n$ such that each $\eta_n$ followed by $DQ.yb_n$ and then by $\mathrm{Spec}$ of $\mathcal O \to \mathcal O/\pi^{n+1}$ is the structure morphism $\mathrm{Spec}$ of $\mathcal O \to R/\pi^{n+1}R$, and such that $\mathrm{Spec}$ of the transition $R/\pi^{n+2}R \to R/\pi^{n+1}R$ followed by $\eta_{n+1}$ equals $\eta_n$ followed by $DQ.yt_n$, there exists an adic point $x$ over $R$ — a compatible family $x.\mathrm{pt}_n$ of Deligne data over $R/\pi^{n+1}R$, each inducing the previous one — with $\eta_n = q_n(\psi_{0,n}, x.\mathrm{pt}_n)$ for all $n$.
--
--   Second, fibres: for adic points $x, x'$ over $R$, one has $q_n(\psi_{0,n}, x.\mathrm{pt}_n) = q_n(\psi_{0,n}, x'.\mathrm{pt}_n)$ for all $n$ if and only if there exists $\gamma \in \Gamma$ such that for every $n$ the pair $(\psi_{0,n}, x'.\mathrm{pt}_n)$ is the $\sigma\gamma$-twisted translate of $(\psi_{0,n}, x.\mathrm{pt}_n)$ over $R/\pi^{n+1}R$, i.e. $\psi_{0,n} = \psi_{0,n} \circ Fr^{-vdet(\sigma\gamma)}$ and, for every full lattice $M$ in $K_0^2$, the line of $x'.\mathrm{pt}_n$ at $M$ is the preimage, under the base-changed action of $(\sigma\gamma)^{-1}$, of the line of $x.\mathrm{pt}_n$ at the transform of $M$ by $(\sigma\gamma)^{-1}$.
--
--   This is the adic half of the Čerednik–Drinfel'd style description of the quotient of the twisted Mumford tower: points of the quotient tower with values in the valuation ring of a complete algebraically closed field over $K_0$ come from adic points of the formal upper half-plane together with the fixed unramified coordinate $\psi_0$, and two such adic points give the same point at every level exactly when they differ by the Frobenius-twisted action of an element of $\Gamma$. It is combined with the corresponding geometric statement about fibres in [`CerednikDrinfeld.FormalOmega.descendedQuotientMap_fib_adicFib`](thm.html#CerednikDrinfeld.FormalOmega.descendedQuotientMap_fib_adicFib).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_descendedQuotientMap_adicFib.lean

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.descendedQuotientMap_adicFib

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

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (N : Subgroup (PGL(2, K₀))) (hNle : N ≤ Γ'.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal) (hNidx : N.relIndex (Γ'.map ρ) ≠ 0)
    (DM : MumfordTower 𝒪 π K₀ r g₁ N)

    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G₂ : Type) [Group G₂] [Finite G₂] (a : ∀ n : ℕ, G₂ →* Aut (X n))
    (pr₁ : ∀ n : ℕ, X n ⟶ DM.Z n) (pr₂ : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
    (θ : ↥Γ →* G₂) (Fr₂ : ∀ n : ℕ, (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1)) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (haff : ∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n)))
    (ha_over : ∀ (n : ℕ) (g : G₂), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G₂), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (hX : ∀ n : ℕ, IsPullback (pr₁ n) (pr₂ n) (DM.zb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hxb : ∀ n : ℕ, xb n = pr₁ n ≫ DM.zb n)
    (hxt₁ : ∀ n : ℕ, xt n ≫ pr₁ (n + 1) = pr₁ n ≫ DM.zt n)
    (hxt₂ : ∀ n : ℕ, xt n ≫ pr₂ (n + 1) = pr₂ n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) (Nat.le_succ (n + 1)))))))
    (hθsurj : Function.Surjective θ) (hθker : ∀ γ : ↥Γ, θ γ = 1 ↔ ρ (γ : G) ∈ N)
    (hFr₂ : ∀ (n : ℕ) (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))), (y' : Onr) = Fr (y : Onr) →
      Fr₂ n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y')
    (ha_pr₂ : ∀ (n : ℕ) (γ : ↥Γ), (a n (θ γ)).hom ≫ pr₂ n =
      pr₂ n ≫ Spec.map (CommRingCat.ofHom ((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toRingEquiv.toRingHom))
    (ha_pr₁ : ∀ (n : ℕ) (γ : ↥Γ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B (σ (γ : G))⁻¹ P P' →
      ∀ x : Spec (CommRingCat.of B) ⟶ X n, x ≫ pr₁ n = DM.q n B hB P → (x ≫ (a n (θ γ)).hom) ≫ pr₁ n = DM.q n B hB P')

    (DQ : TowerQuotientDatum 𝒪 π X xb xt G₂ a)
    (q : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 →
    (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Spec (CommRingCat.of B) ⟶ DQ.Y n))
    (hqdef : (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (ψ : Onr →ₐ[𝒪] B)
        (ψ₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (hψ₂ : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), ψ₂ (Ideal.Quotient.mk _ y) = ψ (y : Onr))
        (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ X n),
        x ≫ pr₁ n = DM.q n B hB P → x ≫ pr₂ n = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) → q n B hB (ψ, P) = x ≫ DQ.p n)) :
    (∀ (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] (Γ₀ : Type) [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
          [CompleteSpace C] [IsAlgClosed C]
          (R : Type) [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
          (ϖ : PseudoUniformizer K₀ C), IsAdicFrame π ϖ R → ∀ (ψ₀ : Onr →ₐ[𝒪] R)
          (hmod : ∀ n : ℕ, (algebraMap 𝒪 (modPow π R n) π) ^ (n + 1) = 0),
        (∀ η : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ DQ.Y n,
          (∀ n : ℕ, η n ≫ DQ.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
            Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (modPow π R n)))) →
          (∀ n : ℕ, Spec.map (CommRingCat.ofHom (modPowTransition π R n).toRingHom) ≫ η (n + 1) = η n ≫ DQ.yt n) →
          ∃ x : AdicPoint K₀ π R, ∀ n : ℕ, η n = q n (modPow π R n) (hmod n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)) ∧
        (∀ x x' : AdicPoint K₀ π R,
          (∀ n : ℕ, q n (modPow π R n) (hmod n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n) = q n (modPow π R n) (hmod n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x'.pt n)) ↔
          ∃ γ ∈ Γ, ∀ n : ℕ, OmegaNr.IsTwistedAct π Onr Fr vdet (modPow π R n) (σ γ) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x'.pt n))) := by sorry
