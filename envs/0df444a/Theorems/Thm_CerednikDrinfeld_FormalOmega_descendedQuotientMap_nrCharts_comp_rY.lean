-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrCharts_comp_rY
-- name    : CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrCharts_comp_rY
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/2c3bfd37-19fb-584a-8d09-53c7119f6693
-- title:
--   Unramified edge charts compute the descended quotient point
-- statement:
--   The setting is that of the Čerednik–Drinfeld construction over a complete discrete valuation ring.
--
--   Coefficients. Fixed are a prime $r$; a characteristic-zero domain $\mathcal{O}$ which is a discrete valuation ring (`hdvr`) with irreducible element $\pi$ (`hπ`), $(\pi)$-adically complete (`hcomplete`), with residue ring of cardinality $r$ (`hres`) and with $(r)=(\pi)$ in $\mathcal{O}$ (`hunr`); and a characteristic-zero field $K_0$ which is the fraction field of $\mathcal{O}$.
--
--   The unramified layer. A characteristic-zero domain $Onr$ over $\mathcal{O}$ together with an $\mathcal{O}$-algebra automorphism $Fr$ is given, subject to: $(\pi Onr)$-adic completeness (`hOnr_complete`), maximality of the ideal $(\pi Onr)$ (`hOnr_max`), every element of $Onr$ satisfying a monic polynomial over $\mathcal{O}$ modulo $\pi$ (`hOnr_alg`), every monic polynomial over $Onr$ of positive degree having a root modulo $\pi$ (`hOnr_closed`), and $Fr(x)\equiv x^{r}\pmod{\pi}$ for all $x$ (`hFr`). Throughout, $\mathcal{O}_2$ denotes the $\mathcal{O}$-subalgebra `AlgHom.equalizer` of $Fr\circ Fr$ and the identity of $Onr$, i.e. the fixed ring of $Fr^{2}$.
--
--   Determinant valuation and groups. A homomorphism $vdet\colon GL_2(K_0)\to\mathbb{Z}$ (written multiplicatively) is given with the property (`hvdet`) that $vdet(g)=n$ if and only if $\det g=u\,\pi^{n}$ for some $u\in\mathcal{O}^{\times}$. Further data: a group $G$, a homomorphism $\sigma\colon G\to GL_2(K_0)$, a subgroup $\Gamma\le G$ containing an element $z$ with $\sigma z$ a scalar matrix and $vdet(\sigma z)=2$ (`hcent`) and an element $w$ with $vdet(\sigma w)=1$ (`hodd`), and a subgroup $\Gamma'$ characterised (`hΓ'`) as the set of $x\in\Gamma$ with $vdet(\sigma x)$ even. The homomorphism $\rho\colon G\to PGL_2(K_0)$ is the projectivisation of $\sigma$ (`hρ`); the image $\rho(\Gamma')$ acts on the vertices of the lattice tree of $\mathcal{O}$ in $K_0$ with finite vertex stabilisers (`hdisc`) and finitely many orbits (`hcocpt`). The matrix $g_1$ is the diagonal matrix $\mathrm{diag}(\pi,1)$ (`hg₁`).
--
--   The Mumford tower and its quotient. A subgroup $N\le\rho(\Gamma')$ (`hNle`) is given whose intersection with $\rho(\Gamma)$ is normal there (`hNnorm`) and which has nonzero relative index in $\rho(\Gamma')$ (`hNidx`), together with a `MumfordTower` $DM$ for $(\mathcal{O},\pi,K_0,r,g_1,N)$, with schemes $Z_n$ over $\mathrm{Spec}(\mathcal{O}/\pi^{n+1})$ and its representability map $DM.q$ on Deligne data. Next come: schemes $X_n$ with structure morphisms $xb_n$ to $\mathrm{Spec}(\mathcal{O}/\pi^{n+1})$ and transitions $xt_n$, a finite group $G_2$ acting by $a_n$, projections $pr_1{}_n\colon X_n\to Z_n$ and $pr_2{}_n\colon X_n\to\mathrm{Spec}(\mathcal{O}_2/\pi^{n+1})$, a homomorphism $\theta\colon\Gamma\to G_2$ and automorphisms $Fr_2$ of the rings $\mathcal{O}_2/\pi^{n+1}$. These are subject to the hypotheses `hcart`, `hproper`, `hflat`, `haff`, `ha_over`, `ha_xt`, `hX`, `hxb`, `hxt₁`, `hxt₂`, `hθsurj`, `hθker`, `hFr₂`, `ha_pr₂`, `ha_pr₁` (summarised here): the tower $(X_n,xb_n,xt_n)$ is cartesian, proper and flat over the truncations of $\mathcal{O}$ with finite sets contained in affine opens, the $G_2$-action is over the base and compatible with the transitions, each $X_n$ is the fibre product of $Z_n$ and $\mathrm{Spec}(\mathcal{O}_2/\pi^{n+1})$ over $\mathrm{Spec}(\mathcal{O}/\pi^{n+1})$ along $pr_1$ and $pr_2$ with the compatibilities $hxb$, $hxt_1$, $hxt_2$, $\theta$ is surjective with kernel the $\gamma\in\Gamma$ with $\rho\gamma\in N$, $Fr_2$ is induced by $Fr$, the automorphism $a_n(\theta\gamma)$ acts on the second factor by $Fr_2^{-vdet(\sigma\gamma)}$ and on the first factor by pullback of Deligne data along $(\sigma\gamma)^{-1}$.
--
--   A `TowerQuotientDatum` $DQ$ for $(\mathcal{O},\pi,X,xb,xt,G_2,a)$ is given, with schemes $Y_n$, base maps $yb_n$, transitions $yt_n$ and the finite surjection $p_n\colon X_n\to Y_n$, together with a map $q$ assigning to each $n$, each $\mathcal{O}$-algebra $B$ with $\pi^{n+1}=0$ and each pair $(\psi,P)$ consisting of an $\mathcal{O}$-algebra homomorphism $\psi\colon Onr\to B$ and a Deligne datum $P$ over $B$ a $B$-point of $Y_n$; the hypotheses on $q$ are: `hqdef`, stating that whenever $x\colon\mathrm{Spec}(B)\to X_n$ satisfies $x$ followed by $pr_1{}_n$ equal to $DM.q(P)$ and $x$ followed by $pr_2{}_n$ equal to $\mathrm{Spec}(\psi_2)$ for the map $\psi_2$ on $\mathcal{O}_2/\pi^{n+1}$ induced by $\psi$, then $q_n(\psi,P)$ is $x$ followed by $p_n$; `hqover` (compatibility with the base), `hqnat` (naturality in $B$), `hqyt` (compatibility with the transitions $yt_n$) and `hqinv` (invariance under the twisted action `OmegaNr.IsTwistedAct` of $\sigma\gamma$ for $\gamma\in\Gamma$, which twists $\psi$ by $Fr^{-vdet(\sigma\gamma)}$ and pulls $P$ back along $(\sigma\gamma)^{-1}$).
--
--   Finally, an unramified presentation $Pr$ of type `MumfordTower.NrPresentation` for the above data with $E=\theta(\Gamma')$ is given, providing schemes $X'_n$ over $\mathrm{Spec}(Onr/\pi^{n+1})$, the morphisms $qX_n\colon X'_n\to X_n$ and the charts $\kappa'_{h,n}$ from $\mathrm{Spec}$ of $A_n:=\mathrm{chartERing}(Onr,\pi,r)/(\pi^{n+1})$ to $X'_n$, indexed by $h\in GL_2(K_0)$; a `TowerQuotientDatum` $D'$ for $(Onr,\pi,X',xb',xt',G_2,a')$ with quotient maps $p'_n$; and comparison morphisms $rY_n\colon D'.Y_n\to DQ.Y_n$ which are cartesian over $\mathrm{Spec}(Onr/\pi^{n+1})\to\mathrm{Spec}(\mathcal{O}/\pi^{n+1})$ (`hrY`), satisfy $p'_n$ followed by $rY_n$ equal to $qX_n$ followed by $p_n$ (`hrY_p`), and commute with the transitions (`hrY_yt`).
--
--   The assertion is the following. For every $h\in GL_2(K_0)$, every $n\in\mathbb{N}$, every commutative ring $B$ carrying compatible $\mathcal{O}$- and $Onr$-algebra structures and satisfying $\pi^{n+1}=0$ in $B$, every $Onr$-algebra homomorphism $\bar x\colon A_n\to B$, and all Deligne data $d,P$ over $B$ (relative to $K_0$ and $\pi$), assume:
--
--   (i) $d$ is the chart datum attached to $\bar x$, in the sense of the three clauses: the line of $d$ at the standard full lattice $L$ of $K_0^2$ is the $B$-span of $\bar x(\xi)\otimes e_0+1\otimes e_1$, where $\xi$ is the class of `chartERing.ξ` and $e_0,e_1$ are the standard basis vectors of $L$; the line of $d$ at $g_1\cdot L$ is the image under `actBaseChange` for $g_1$ of the $B$-span of $1\otimes e_0+\bar x(\eta)\otimes e_1$, with $\eta$ the class of `chartERing.η`; and $d$ satisfies `DeligneDatum.InEdgeChart` for the pair $(g_1\cdot L,L)$, i.e. for every prime ideal $\mathfrak{p}$ of $B$ the edge-nondegeneracy conditions of `EdgeNondegAt` hold at $\mathfrak{p}$ for this pair of lattices.
--
--   (ii) $P$ is the pullback of $d$ along $h^{-1}$: for every full lattice $M$, the line of $P$ at $M$ is the preimage of the line of $d$ at $h^{-1}\cdot M$ under the base-changed action isomorphism for $h^{-1}$.
--
--   Then $\mathrm{Spec}(\bar x)$ followed by $\kappa'_{h,n}$, then by $p'_n$, then by $rY_n$, equals $q_n(B,(\iota,P))$, where $\iota\colon Onr\to B$ is the structural $\mathcal{O}$-algebra map of the scalar tower.
--
--   This identifies, on the unramified layer of the Čerednik–Drinfeld tower, the composite of an edge chart with the quotient map $p'_n$ and the comparison morphism $rY_n$ with the functorially defined point $q_n$ of the descended quotient at the chart's Deligne datum; the coefficient ring is the edge chart ring over $Onr$ truncated modulo $\pi^{n+1}$. It is the chart-level input for [`CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrCharts`](thm.html#CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrCharts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrCharts_comp_rY.lean

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_CerednikDrinfeld_MumfordNrPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrCharts_comp_rY

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
        x ≫ pr₁ n = DM.q n B hB P → x ≫ pr₂ n = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) → q n B hB (ψ, P) = x ≫ DQ.p n))
    (hqover : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q n B hB x ≫ DQ.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B)))
    (hqnat : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B')
    (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q n B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ q n B hB x)
    (hqyt : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (hB' : (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q (n + 1) B hB' x = q n B hB x ≫ DQ.yt n)
    (hqinv : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (γ : G), γ ∈ Γ →
    ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
      OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → q n B hB x' = q n B hB x)

    (Pr : MumfordTower.NrPresentation 𝒪 π K₀ g₁ N DM Onr Fr X xb xt G₂ a pr₁ pr₂ ((Γ'.subgroupOf Γ).map θ))
    (D' : TowerQuotientDatum Onr (algebraMap 𝒪 Onr π) Pr.X' Pr.xb' Pr.xt' G₂ Pr.a')
    (rY : ∀ n : ℕ, D'.Y n ⟶ DQ.Y n)
    (hrY : ∀ n : ℕ, IsPullback (rY n) (D'.yb n) (DQ.yb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hrY_p : ∀ n : ℕ, D'.p n ≫ rY n = Pr.qX n ≫ DQ.p n)
    (hrY_yt : ∀ n : ℕ, D'.yt n ≫ rY (n + 1) = rY n ≫ DQ.yt n)
    :
    (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
          (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
          (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
          DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
          Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ (Pr.κ' h n ≫ D'.p n) ≫ rY n = q n B hB ((IsScalarTower.toAlgHom 𝒪 Onr B), P)) := by sorry
