-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrCharts
-- name    : CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrCharts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/bf4e2504-4a18-5fe3-a947-337f3a5e4d27
-- title:
--   Charts of the unramified layer of the descended Čerednik–Drinfeld tower
-- statement:
--   Throughout, $r$ is a prime number and $\mathcal{O}$ is a characteristic-zero domain which is a discrete valuation ring (`hdvr`), $\pi \in \mathcal{O}$ is irreducible (`hπ`), $\mathcal{O}$ is $\pi$-adically complete (`hcomplete`), the residue ring $\mathcal{O}/(\pi)$ has exactly $r$ elements (`hres`), and $(r) = (\pi)$ as ideals of $\mathcal{O}$ (`hunr`); $K_0$ is a characteristic-zero field which is a fraction field of $\mathcal{O}$.
--
--   **Unramified coefficients and the valuation of the determinant.** $O^{\mathrm{nr}}$ is a characteristic-zero domain and an $\mathcal{O}$-algebra, $\mathrm{Fr}$ an $\mathcal{O}$-algebra automorphism of it, subject to: $O^{\mathrm{nr}}$ is $\pi$-adically complete (`hOnr_complete`), $(\pi)$ is maximal in $O^{\mathrm{nr}}$ (`hOnr_max`), every element of $O^{\mathrm{nr}}$ satisfies a monic polynomial over $\mathcal{O}$ modulo $(\pi)$ (`hOnr_alg`), every monic polynomial over $O^{\mathrm{nr}}$ of positive degree has a root modulo $(\pi)$ (`hOnr_closed`), and $\mathrm{Fr}(x) \equiv x^{r} \pmod{(\pi)}$ for all $x$ (`hFr`). The homomorphism $\mathrm{vdet} : \mathrm{GL}_2(K_0) \to \mathbb{Z}$ (written multiplicatively) satisfies `hvdet`: $\mathrm{vdet}(g) = n$ if and only if $\det g = u\pi^{n}$ for some unit $u$ of $\mathcal{O}$.
--
--   **The group data.** $G$ is a group, $\sigma : G \to \mathrm{GL}_2(K_0)$ a homomorphism, $\Gamma \le G$ a subgroup containing a central element $z$ with $\sigma z$ a scalar matrix and $\mathrm{vdet}(\sigma z) = 2$ (`hcent`) and an element $w$ with $\mathrm{vdet}(\sigma w) = 1$ (`hodd`); $\Gamma'$ is the subgroup whose members are exactly the elements of $\Gamma$ with $\mathrm{vdet} \circ \sigma$ even (`hΓ'`). The homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ is the projectivisation of $\sigma$ (`hρ`); the image $\rho(\Gamma')$ acts on the vertices of the lattice tree of $\mathcal{O}$ in $K_0$ with finite vertex stabilisers (`hdisc`) and with finitely many orbits, witnessed by a finite set of vertices meeting every orbit (`hcocpt`). The matrix $g_1$ is $\mathrm{diag}(\pi, 1)$ (`hg₁`). Finally $N \le \mathrm{PGL}_2(K_0)$ satisfies $N \le \rho(\Gamma')$ (`hNle`), $N \cap \rho(\Gamma)$ is normal in $\rho(\Gamma)$ (`hNnorm`), and the relative index of $N$ in $\rho(\Gamma')$ is nonzero (`hNidx`); $DM$ is a `MumfordTower` $\mathcal{O}$, $\pi$, $K_0$, $r$, $g_1$, $N$, so a tower of schemes $DM.Z_n$ over $\mathcal{O}/(\pi^{n+1})$ with cartesian transitions, proper and flat structure maps, affine neighbourhoods of finite sets, and a system of moduli maps $DM.q$ from Deligne data that is functorial, compatible with the transitions, and invariant under the elements of $N$.
--
--   **The twisted tower.** $X : \mathbb{N} \to \mathrm{Sch}$ with structure maps $xb_n : X_n \to \operatorname{Spec}(\mathcal{O}/(\pi^{n+1}))$ and transitions $xt_n : X_n \to X_{n+1}$; $G_2$ is a finite group acting by $a_n : G_2 \to \mathrm{Aut}(X_n)$; $pr_{1,n} : X_n \to DM.Z_n$ and $pr_{2,n} : X_n \to \operatorname{Spec}(\mathcal{O}_2/(\pi^{n+1}))$, where $\mathcal{O}_2 =$ `AlgHom.equalizer` of $\mathrm{Fr} \circ \mathrm{Fr}$ and the identity, i.e. the $\mathcal{O}$-subalgebra of $O^{\mathrm{nr}}$ fixed by $\mathrm{Fr}^2$; $\theta : \Gamma \to G_2$ is a homomorphism and $\mathrm{Fr}_{2,n}$ an $\mathcal{O}$-algebra automorphism of $\mathcal{O}_2/(\pi^{n+1})$. The hypotheses on these data are: the transition squares of $X$ over the maps $\mathcal{O}/(\pi^{n+2}) \to \mathcal{O}/(\pi^{n+1})$ are pullbacks (`hcart`), each $xb_n$ is proper (`hproper`) and flat (`hflat`), every finite subset of $X_n$ lies in an affine open (`haff`), the automorphisms $a_n(g)$ lie over the base (`ha_over`) and commute with the transitions (`ha_xt`), each square $(pr_{1,n}, pr_{2,n}, DM.zb_n, \operatorname{Spec}$ of $\mathcal{O}/(\pi^{n+1}) \to \mathcal{O}_2/(\pi^{n+1}))$ is a pullback (`hX`), $xb_n = pr_{1,n}$ followed by $DM.zb_n$ (`hxb`), and $pr_1$, $pr_2$ are compatible with the transitions (`hxt₁`, `hxt₂`); $\theta$ is surjective (`hθsurj`) with $\theta(\gamma) = 1$ exactly when $\rho(\gamma) \in N$ (`hθker`); $\mathrm{Fr}_{2,n}$ is induced by $\mathrm{Fr}$ on residue classes (`hFr₂`); $a_n(\theta\gamma)$ followed by $pr_{2,n}$ equals $pr_{2,n}$ followed by $\operatorname{Spec}$ of $\mathrm{Fr}_{2,n}^{-\mathrm{vdet}(\sigma\gamma)}$ (`ha_pr₂`); and, for $\gamma \in \Gamma$, $B$ an $\mathcal{O}$-algebra in which $\pi^{n+1} = 0$, and Deligne data $P, P'$ over $B$ with $P'$ the pullback of $P$ along $\sigma(\gamma)^{-1}$, any $x : \operatorname{Spec} B \to X_n$ with $x \circ pr_{1,n}$ classifying $P$ has $a_n(\theta\gamma) \circ x$ followed by $pr_{1,n}$ classifying $P'$ (`ha_pr₁`).
--
--   **The quotient datum.** $DQ$ is a `TowerQuotientDatum` for $\mathcal{O}, \pi, X, xb, xt, G_2, a$: a tower $DQ.Y_n$ over $\mathcal{O}/(\pi^{n+1})$ with cartesian transitions, proper and flat structure maps, together with $G_2$-invariant finite surjective maps $DQ.p_n : X_n \to DQ.Y_n$ forming pullback squares with the transitions, locally epimorphic, and satisfying the local universal property of the quotient. The family $q$ assigns to each $n$, each $\mathcal{O}$-algebra $B$ with $\pi^{n+1} = 0$ and each pair $(\psi, P)$ consisting of an $\mathcal{O}$-algebra map $\psi : O^{\mathrm{nr}} \to B$ and a Deligne datum $P$ over $B$ for $(K_0,\pi)$, a morphism $\operatorname{Spec} B \to DQ.Y_n$. It is subject to: `hqdef`, which identifies $q_n(\psi, P)$ with $x$ followed by $DQ.p_n$ whenever $x : \operatorname{Spec} B \to X_n$ satisfies $x \circ pr_{1,n} = DM.q_n(P)$ and $x \circ pr_{2,n} = \operatorname{Spec}(\psi_2)$ for an $\mathcal{O}$-algebra map $\psi_2$ on $\mathcal{O}_2/(\pi^{n+1})$ induced by $\psi$; `hqover`, compatibility of $q$ with the structure maps over $\operatorname{Spec}\mathcal{O}$; `hqnat`, naturality in $B$; `hqyt`, compatibility with the transitions $DQ.yt_n$; and `hqinv`, invariance under the twisted action: for $\gamma \in \Gamma$ and pairs $x, x'$ with $x'_1 = x_1 \circ \mathrm{Fr}^{-\mathrm{vdet}(\sigma\gamma)}$ and $x'_2$ the pullback of $x_2$ along $\sigma(\gamma)^{-1}$, one has $q_n(x') = q_n(x)$.
--
--   **The unramified presentation and its quotient.** $Pr$ is a `MumfordTower.NrPresentation` for these data with distinguished subgroup $\theta(\Gamma' \cap \Gamma) \le G_2$: it provides a tower $Pr.X'_n$ over $O^{\mathrm{nr}}/(\pi^{n+1})$ with transitions and $G_2$-action $Pr.a'$, maps $Pr.qX_n : Pr.X'_n \to X_n$ making the base squares pullbacks and compatible with transitions and with the actions, and charts $Pr.\kappa'(h, n) : \operatorname{Spec} A_n \to Pr.X'_n$ for $h \in \mathrm{GL}_2(K_0)$, where $A_n = A/(\pi^{n+1})$ with $A =$ `chartERing` $O^{\mathrm{nr}}$ $\pi$ $r$, the localisation of the quotient of $O^{\mathrm{nr}}[\,\text{two variables}\,]$ by the relation `edgeRel` at the element `edgeQuot.discr`, carrying the two distinguished elements `chartERing.ξ` and `chartERing.η`. Further, $D'$ is a `TowerQuotientDatum` for $O^{\mathrm{nr}}$, $\pi$, $Pr.X'$, $Pr.xb'$, $Pr.xt'$, $G_2$, $Pr.a'$, and $rY_n : D'.Y_n \to DQ.Y_n$ are morphisms such that each square $(rY_n, D'.yb_n, DQ.yb_n, \operatorname{Spec}$ of $\mathcal{O}/(\pi^{n+1}) \to O^{\mathrm{nr}}/(\pi^{n+1}))$ is a pullback (`hrY`), $D'.p_n$ followed by $rY_n$ equals $Pr.qX_n$ followed by $DQ.p_n$ (`hrY_p`), and $D'.yt_n$ followed by $rY_{n+1}$ equals $rY_n$ followed by $DQ.yt_n$ (`hrY_yt`).
--
--   **Conclusion.** Write $\kappa_{h,n}$ for $Pr.\kappa'(h,n)$ followed by $D'.p_n$, a morphism $\operatorname{Spec} A_n \to D'.Y_n$. Then the following four statements hold for all $h \in \mathrm{GL}_2(K_0)$ and all $n \in \mathbb{N}$, and the fifth for all $n$.
--
--   (i) The image of the underlying continuous map of $\kappa_{h,n}$ is open in $D'.Y_n$.
--
--   (ii) (Chart law.) For every commutative ring $B$ that is an $\mathcal{O}$-algebra and an $O^{\mathrm{nr}}$-algebra compatibly (scalar tower) with $\pi^{n+1} = 0$ in $B$, every $O^{\mathrm{nr}}$-algebra map $\bar{x} : A_n \to B$ and all Deligne data $d, P$ over $B$ for $(K_0,\pi)$: if $d$ satisfies the chart equations
--   $$d.\mathrm{line}(L_0) = B\cdot\big(\bar{x}(\xi) \otimes e_0 + 1 \otimes e_1\big), \qquad d.\mathrm{line}(g_1 \cdot L_0) = \big(B\cdot(1 \otimes e_0 + \bar{x}(\eta) \otimes e_1)\big)\ \text{transported by}\ g_1,$$
--   where $L_0$ is the standard full lattice, $e_0, e_1$ its standard basis vectors, $\xi, \eta$ the classes of `chartERing.ξ`, `chartERing.η` in $A_n$ and the transport is along `actBaseChange` $B$ $g_1$ $L_0$, and if moreover $d$ is in the edge chart for the pair $(g_1 \cdot L_0, L_0)$, i.e. for every prime ideal $\mathfrak{p}$ of $B$ one has $g_1 \cdot L_0 \subseteq L_0$, $\pi L_0 \subseteq g_1 \cdot L_0$, no $v \in L_0 \setminus g_1\cdot L_0$ has $1 \otimes v \in d.\mathrm{line}(L_0) + \mathfrak{p}\cdot{\top}$, and no $v' \in g_1 \cdot L_0$ outside $\pi L_0$ has $1 \otimes v' \in d.\mathrm{line}(g_1\cdot L_0) + \mathfrak{p}\cdot{\top}$; and if $P$ is the pullback of $d$ along $h^{-1}$, that is $P.\mathrm{line}(M) = (d.\mathrm{line}(h^{-1}\cdot M))$ pulled back along `actBaseChange` $B$ $h^{-1}$ $M$ for every full lattice $M$ — then $\operatorname{Spec}(\bar{x})$ followed by $\kappa_{h,n}$ followed by $rY_n$ equals $q_n(\iota, P)$, where $\iota : O^{\mathrm{nr}} \to B$ is the structural $\mathcal{O}$-algebra map.
--
--   (iii) (Transitions.) $\kappa_{h,n}$ followed by $D'.yt_n$ equals $\operatorname{Spec}$ of the reduction $A_{n+1} \to A_n$ followed by $\kappa_{h,n+1}$.
--
--   (iv) The image of $\kappa_{h,n}$ is the preimage, under the underlying map of $D'.yt_n$, of the image of $\kappa_{h,n+1}$.
--
--   (v) (Covering.) For each $n$, the union over all $h \in \mathrm{GL}_2(K_0)$ of the images of the underlying maps of $\kappa_{h,n}$ is the whole of $D'.Y_n$.
--
--   This is the chart description of the unramified layer of the quotient tower arising in the Čerednik–Drinfeld uniformisation: the composites of the charts of an unramified presentation of the twisted Mumford tower with the quotient map $X' \to Y'$ have open images, obey the expected moduli equation after base change back to the $\mathcal{O}$-level quotient, are compatible with the transitions of the tower, and cover each level. It combines the open-image and covering statement `descendedQuotientMap_nrCharts_isOpen_and_cover`, the chart law `descendedQuotientMap_nrCharts_comp_rY` and the transition compatibility `descendedQuotientMap_nrCharts_transition`, and is used by `descendedQuotientMap_unramifiedLayer`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrCharts.lean

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

theorem CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrCharts

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
    (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), IsOpen (Set.range (Pr.κ' h n ≫ D'.p n).base)) ∧
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
          Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ (Pr.κ' h n ≫ D'.p n) ≫ rY n = q n B hB ((IsScalarTower.toAlgHom 𝒪 Onr B), P)) ∧
    (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
        (Pr.κ' h n ≫ D'.p n) ≫ D'.yt n = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
            (pow_dvd_pow (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) (Nat.le_succ (n + 1)))))) ≫ (Pr.κ' h (n + 1) ≫ D'.p (n + 1))) ∧
    (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
        Set.range (Pr.κ' h n ≫ D'.p n).base = (D'.yt n).base ⁻¹' Set.range (Pr.κ' h (n + 1) ≫ D'.p (n + 1)).base) ∧
    (∀ n : ℕ, ⋃ h : Matrix.GeneralLinearGroup (Fin 2) K₀, Set.range (Pr.κ' h n ≫ D'.p n).base = Set.univ) := by sorry
