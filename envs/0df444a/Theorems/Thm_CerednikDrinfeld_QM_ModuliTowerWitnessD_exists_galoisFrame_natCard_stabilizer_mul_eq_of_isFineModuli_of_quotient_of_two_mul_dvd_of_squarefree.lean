-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_galoisFrame_natCard_stabilizer_mul_eq_of_isFineModuli_of_quotient_of_two_mul_dvd_of_squarefree
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_galoisFrame_natCard_stabilizer_mul_eq_of_isFineModuli_of_quotient_of_two_mul_dvd_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/8abbab38-3d3c-5555-a6dc-885cbf978c16
-- title:
--   Galois frame and stabiliser balance for the level-ℓ leg
-- statement:
--   **Arithmetic data.** Fix a nonzero natural number $N$ and primes $q,q'$ with $q'\neq q$, $q\nmid N$, $q'\nmid N$ and $N$ squarefree, and a natural number $D$ with $2Nqq'\mid D$. Fix rationals $a,b$ for which `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a>0$ or $b>0$ and, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit exactly when $q\in v$ or $q'\in v$. Fix a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ which is a maximal order: it contains $1$, is closed under multiplication, spans $\mathbb H[\mathbb Q,a,b]$ over $\mathbb Q$, is finitely generated, and is not properly contained in another such order.
--
--   Throughout, a *fake elliptic curve* over a commutative ring $S$ (the project's `FakeEllipticCurve Λ N S`) is an abelian scheme $A\to\operatorname{Spec}S$ with commutative relative group law, two-dimensional fibres, a $\Lambda$-action satisfying the prescribed additivity and trace conditions, and a level-$N$ structure `lev`; a *place* of a field extension over a base field is a valuation subring containing the base, distinct from the whole field, whose value group makes it a principal ideal ring.
--
--   **The base moduli datum over $\mathbb Z[1/D]$ and the tower.** Fix a field $\bar F$ (`Fbar`) which is an algebra over $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ`, a curve over $\overline{\mathbb Q}$ in the sense of `IsCurveOver` (principal divisors, finite residue extensions, $\Omega$ free of rank one) and essentially of finite type over $\overline{\mathbb Q}$; a scheme $X$ with a morphism $\pi_X$ to $\operatorname{Spec}\mathbb Z[1/D]$; a $\overline{\mathbb Q}$-point $\bar s$ of $\operatorname{Spec}\mathbb Z[1/D]$; and a rule $\mathrm{pt}$ assigning to each commutative ring $S$, each morphism $s\colon\operatorname{Spec}S\to\operatorname{Spec}\mathbb Z[1/D]$ and each fake elliptic curve over $S$ a section of $\pi_X$ over $s$. The hypotheses `pt_iso`, `pt_pullback`, `pt_surjective`, `pt_injective` are the four representability clauses of a coarse moduli rule (invariance under `FakeEllipticCurve.Iso`, compatibility with base change along ring maps and `FakeEllipticCurve.IsPullback`, and bijectivity on isomorphism classes over algebraically closed fields); the universal property of `IsCoarseModuli` is not assumed for $X$.
--
--   Further data: a curve model $\mathfrak M$ of $\bar F$ over $\overline{\mathbb Q}$ together with an isomorphism $e_{\mathfrak M}\colon\mathfrak M.C\to X\times_{\mathbb Z[1/D]}\overline{\mathbb Q}$ such that $e_{\mathfrak M}$ followed by the second projection is $\mathfrak M.\mathrm{toBase}$; a monoid homomorphism $\mathrm{gal}$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to the semilinear automorphisms of $\bar F$ over $\overline{\mathbb Q}$; tower data $\mathbb T$ of type `HeckeTower.TowerData q q' Fbar`, consisting of curve function fields $\mathbb T.F_\ell$ indexed by the primes $\ell\neq q,q'$ together with finite integral $\overline{\mathbb Q}$-algebra maps $\mathbb T.\varphi_\alpha$ from $\bar F$; Galois actions $\mathrm{gal}_{\mathbb T}$ on each $\mathbb T.F_\ell$; families $W$ and $W_{\mathbb T}$ of two semilinear automorphisms each, of $\bar F$ and of the $\mathbb T.F_\ell$; and a witness $tw$ of type `ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT`, which ties all of these together (its clauses are those of that structure). Finally fix a prime $\ell$ with $\ell\neq q,q'$.
--
--   **The coarse curve of pairs over $\overline{\mathbb Q}$.** Fix an integral scheme $Y$ with a separated, smooth of relative dimension one morphism $\pi_Y$ to $\operatorname{Spec}\overline{\mathbb Q}$, and a rule $\mathrm{pt}_{\mathbb T}$ on pairs (fake elliptic curve together with an `ExtraLevel` at $\ell$: a closed subscheme of the abelian scheme, finite flat of rank $\ell^2$ over the base, killed by $\ell$, stable under $\Lambda$, disjoint from `lev`, with geometric fibres isomorphic to $(\mathbb Z/\ell)^2$), such that $h_Y$: $(Y,\pi_Y,\mathrm{pt}_{\mathbb T})$ is a coarse moduli space for such pairs in the sense of `IsCoarseModuliT` (the four representability clauses and the universal property). Fix a morphism $d_0\colon Y\to X$ with $h_{d_0}$: for all $S$, all $s\colon\operatorname{Spec}S\to\operatorname{Spec}\overline{\mathbb Q}$ and all pairs $u$, the section $\mathrm{pt}_{\mathbb T}(u)$ followed by $d_0$ equals $\mathrm{pt}$ of the underlying curve $u.1$ over $s$ followed by $\bar s$. Fix a curve model $\mathfrak M_\ell$ of $\mathbb T.F_\ell$ over $\overline{\mathbb Q}$ and an isomorphism $e_\ell\colon\mathfrak M_\ell.C\to Y$ with $e_\ell$ followed by $\pi_Y$ equal to $\mathfrak M_\ell.\mathrm{toBase}$, and the compatibility $h_{\mathrm{compat}_0}$: for every place $R'$ of $\mathbb T.F_\ell$ over $\overline{\mathbb Q}$, the $\overline{\mathbb Q}$-point of $\mathfrak M_\ell.C$ corresponding to $R'$ under `pointEquivPlace`, followed by $e_\ell$ and $d_0$, equals the $\overline{\mathbb Q}$-point of $\mathfrak M.C$ corresponding to the restriction of $R'$ along $\mathbb T.\varphi_{(\ell,0)}$, followed by $e_{\mathfrak M}$ and the first projection.
--
--   **The point under consideration.** Fix a place $R$ of $\mathbb T.F_\ell$ over $\overline{\mathbb Q}$ and a fake elliptic curve $E$ over $\overline{\mathbb Q}$ with $h_E$: $\mathrm{pt}(E)$ over $\bar s$ equals the $\overline{\mathbb Q}$-point of $\mathfrak M.C$ attached to the restriction of $R$ along $\mathbb T.\varphi_{(\ell,0)}$, followed by $e_{\mathfrak M}$ and the first projection. Fix $n$ and an enumeration $K\colon \mathrm{Fin}\,n\to E.\mathrm{ExtraLevel}\,\ell$ which, by $h_{K\mathrm{dist}}$, is injective up to the relation 'the predicates `FactorsThrough (K i).levK` and `FactorsThrough (K j).levK` agree on all $\overline{\mathbb Q}$-points of $E$', and which, by $h_{K\mathrm{exh}}$, exhausts all extra levels up to that same relation.
--
--   **The fine cover at full level $m$.** Fix $m$ with $m$ invertible in $\overline{\mathbb Q}$ and $\ell\mid m$ ($h_{\ell m}$), a scheme $M$ with $\pi_M\colon M\to\operatorname{Spec}\overline{\mathbb Q}$ and a rule $\mathrm{pt}_F$ on pairs (fake elliptic curve, full level-$m$ structure: a section $P$ with $mP=0$ generating the $m$-torsion under $\Lambda$ and with the prescribed annihilator condition), such that $h_M$: $(M,\pi_M,\mathrm{pt}_F)$ is a fine moduli space in the sense of `IsFineModuli` (iso-invariance, base change, and bijectivity of $\mathrm{pt}_F$ on $S$-points for every $S$). Assume $\pi_M$ separated, locally of finite type and smooth of relative dimension one, and $h_{M\mathrm{aff}}$: every finite set of points of $M$ lies in an affine open. Fix a finite group $G$, a homomorphism $\rho\colon G\to\operatorname{Aut}M$ and a map $\chi\colon G\to\Lambda$ with $h_\rho$: `IsLevelTwistAction` (each $\rho g$ lies over the base; twisting a full level structure by $\chi g$ moves $\mathrm{pt}_F$ by $\rho g$; and the clauses making $\chi$ a bijection onto the relevant classes modulo $m$).
--
--   Fix a $\mathbb Z$-submodule $L_0\subseteq\Lambda$ with $\ell\Lambda\subseteq L_0$, stable under left multiplication by $\Lambda$, of relative index $\ell^2$ in $\Lambda$ as additive groups, and a subgroup $H\leq G$ characterised by $h_H$: $g\in H$ if and only if $L_0\cdot\chi g\subseteq L_0$.
--
--   **The two quotients.** Fix $X_q$ with $\pi_{X_q}\colon X_q\to\operatorname{Spec}\overline{\mathbb Q}$ and $\pi_q\colon M\to X_q$ over the base, invariant under all $\rho g$, and satisfying the quotient clauses for $G$ (summarised here): $\pi_q$ is integral, affine and surjective on points, its fibres are the $G$-orbits, it is injective on sections, the image of each $\pi_q^{\#}$ is exactly the $G$-invariant sections, $G$-invariant affine opens of $M$ are preimages of affine opens of $X_q$, and $\pi_q$ is the categorical quotient. Fix a coarse rule $\mathrm{pt}_q$ on $X_q$ with $h_{X_q}$: `IsCoarseModuli`, and $h_{\mathrm{pt}_q}$: $\mathrm{pt}_q$ of the underlying curve of a full level structure equals $\mathrm{pt}_F$ followed by $\pi_q$. Fix an isomorphism $g_X\colon X_q\to X\times_{\mathbb Z[1/D]}\overline{\mathbb Q}$ with $g_X$ followed by the second projection equal to $\pi_{X_q}$ and with $\mathrm{pt}_q$ followed by $g_X$ and the first projection equal to $\mathrm{pt}$ over $s$ followed by $\bar s$.
--
--   Fix likewise $X_H$ with $\pi_{X_H}$ and $\pi_H\colon M\to X_H$ over the base, invariant under all $h\in H$, and satisfying the same eight quotient clauses for $H$ in place of $G$ (integrality, affineness, surjectivity, orbit description of fibres, injectivity on sections, invariant-section image, descent of invariant affine opens, categorical quotient; summarised here), together with a morphism $d_H\colon X_H\to X_q$ with $\pi_H$ followed by $d_H$ equal to $\pi_q$.
--
--   **The subscheme of pairs inside $X_H$.** Fix an open $U\subseteq X_H$ whose underlying set is closed, together with a rule $\mathrm{pt}_U$ on pairs over $U$ such that $h_U$: $(U,U.\iota$ followed by $\pi_{X_H},\mathrm{pt}_U)$ is a coarse moduli space for pairs in the sense of `IsCoarseModuliT`. Assume $h_{U\mathrm{pt}_F}$: whenever $u$ is a full level-$m$ structure over $S$ and $K'$ an extra level at $\ell$ on $u.1$ such that, for every algebraically closed field $k$, every $S\to k$ and every $k$-point $Q$ of $u.1$, $Q$ factors through $K'.\mathrm{levK}$ if and only if $Q=x\cdot\bigl((m/\ell)\,P_u\bigr)$ for some $x\in\Lambda$ lying in $L_0$ (the $\Lambda$-action being `pushPt` and the multiple `nsmulPt`), then $\mathrm{pt}_U\langle u.1,K'\rangle$ followed by $U.\iota$ equals $\mathrm{pt}_F(u)$ followed by $\pi_H$. Assume $h_{Ud}$: $\mathrm{pt}_U(v)$ followed by $U.\iota$ and $d_H$ equals $\mathrm{pt}_q(v.1)$; and $h_{U\mathrm{top}}$: if $\ell\nmid N$ then $U=\top$. Fix an isomorphism $g_U\colon U\to Y$ with $g_U$ followed by $\pi_Y$ equal to $U.\iota$ followed by $\pi_{X_H}$, and $\mathrm{pt}_{\mathbb T}=\mathrm{pt}_U$ followed by $g_U$.
--
--   **The distinguished fine point.** Fix a full level-$m$ structure $P$ on $E$ and an index $i_0$ such that $h_{K_0}$: for every algebraically closed field $k'$, every ring map $\overline{\mathbb Q}\to k'$ and every $k'$-point $Q$ of $E$, $Q$ factors through $(K\,i_0).\mathrm{levK}$ if and only if $Q=x\cdot\bigl((m/\ell)\,P\bigr)$ for some $x\in\Lambda$ lying in $L_0$; and $h_{\mathrm{pt}_0}$: $\mathrm{pt}_{\mathbb T}$ of the pair $\langle E,K\,i_0\rangle$ over $\operatorname{Spec}\overline{\mathbb Q}$ equals the $\overline{\mathbb Q}$-point of $\mathfrak M_\ell.C$ attached to $R$, followed by $e_\ell$.
--
--   **Conclusion.** There exist a field $M_f$ carrying algebra structures over $\overline{\mathbb Q}$, over $\bar F$ and over $\mathbb T.F_\ell$, with $\overline{\mathbb Q}\subseteq\bar F\subseteq M_f$ and $\overline{\mathbb Q}\subseteq\mathbb T.F_\ell\subseteq M_f$ scalar towers, $M_f$ finite-dimensional over $\bar F$ and over $\mathbb T.F_\ell$ and Galois over $\bar F$, and a place $c$ of $M_f$ over $\overline{\mathbb Q}$, such that:
--
--   (i) for every $x\in\bar F$, the image of $x$ under the structure map $\bar F\to M_f$ equals the image of $\mathbb T.\varphi_{(\ell,0)}(x)$ under $\mathbb T.F_\ell\to M_f$;
--
--   (ii) the restriction of $c$ to $\mathbb T.F_\ell$ equals $R$;
--
--   (iii) the product of the cardinality of $\{\sigma\in\operatorname{Gal}(M_f/\bar F): \sigma$, regarded through `SemilinearAut.ofAlgAut` as a semilinear automorphism over $\overline{\mathbb Q}$, fixes $c\}$ with the cardinality of $\{g\in G: g\in H$ and $\mathrm{pt}_F\langle E,P\rangle$ followed by $\rho g$ equals $\mathrm{pt}_F\langle E,P\rangle\}$ equals the product of the cardinality of $\{\sigma\in\operatorname{Aut}_{\mathbb T.F_\ell}(M_f): \sigma$, regarded in the same way, fixes $c\}$ with the cardinality of $\{g\in G: \mathrm{pt}_F\langle E,P\rangle$ followed by $\rho g$ equals $\mathrm{pt}_F\langle E,P\rangle\}$.
--
--   Thus the two decomposition cardinalities at $c$, over $\bar F$ and over $\mathbb T.F_\ell$, are balanced against the orders of the stabiliser of the fine moduli point $\mathrm{pt}_F\langle E,P\rangle$ inside $H$ and inside $G$.
--
--   This is the Galois-frame step for the forgetful (degeneracy) leg at a prime $\ell\neq q,q'$ in the Čerednik–Drinfeld tower of Shimura curves attached to the indefinite quaternion algebra ramified exactly at $q,q'$: it produces a finite extension $M_f$, Galois over the function field of the base curve and containing the function field at level $\ell$ compatibly with $\mathbb T.\varphi_{(\ell,0)}$, with a chosen place above $R$, and records the numerical balance between decomposition groups upstairs and automorphism stabilisers of the corresponding point on the fine level-$m$ cover. It is the version in which the fine cover, the two quotients $M/G$ and $M/H$, the coarse rules and the identifications $U\cong Y$, $M/G\cong X\times\overline{\mathbb Q}$ are taken as hypotheses; it is used by the companion statement [`CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_galoisFrame_natCard_stabilizer_mul_eq_of_two_mul_dvd_of_squarefree`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_galoisFrame_natCard_stabilizer_mul_eq_of_two_mul_dvd_of_squarefree), which supplies those data, in the ramification computations for the tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_galoisFrame_natCard_stabilizer_mul_eq_of_isFineModuli_of_quotient_of_two_mul_dvd_of_squarefree.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicGeometry
open AlgebraicCurve

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_galoisFrame_natCard_stabilizer_mul_eq_of_isFineModuli_of_quotient_of_two_mul_dvd_of_squarefree
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hNsq : Squarefree N)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (x : SchemeHomOver s πX), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')

    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)
    (gal : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)
    (ℓ : HeckeTower.AwayPrime q q')

    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) [IsIntegral Y] [IsSeparated πY]
    (hYsm : SmoothOfRelativeDimension 1 πY)
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s πY)
    (hY : IsCoarseModuliT Λ N (ℓ.1 : ℕ) Y πY ptT)
    (d₀ : Y ⟶ X)
    (hd₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT S s u).1 ≫ d₀ = (pt S (s ≫ sbar) u.1).1)
    (𝔐ℓ : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) (𝕋.F ℓ)) (eℓ : 𝔐ℓ.C ⟶ Y) [IsIso eℓ] (heℓ : eℓ ≫ πY = 𝔐ℓ.toBase)
    (hcompat₀ : ∀ R : Place (AlgebraicClosure ℚ) (𝕋.F ℓ),
      (𝔐ℓ.pointEquivPlace.symm R).1 ≫ eℓ ≫ d₀ = (𝔐.pointEquivPlace.symm (R.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar)

    (R : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)) (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (hE : (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm (R.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar)
    (n : ℕ) (K : Fin n → E.ExtraLevel (ℓ.1 : ℕ))
    (hKdist : ∀ i j : Fin n,
      (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
        FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j)
    (hKexh : ∀ K' : E.ExtraLevel (ℓ.1 : ℕ), ∃ i : Fin n,
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
        FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x)

    (m : ℕ) (hmU : IsUnit ((m : ℕ) : (AlgebraicClosure ℚ)))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF)
    (hMsep : IsSeparated πM) (hMlft : LocallyOfFiniteType πM) (hMsm : SmoothOfRelativeDimension 1 πM)
    (hMaff : ∀ F : Finset M, ∃ W : M.Opens, IsAffineOpen W ∧ ∀ x ∈ F, x ∈ W)
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut M) (χ : G → ↥Λ)
    (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)
    (hℓm : (ℓ.1 : ℕ) ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, ((ℓ.1 : ℕ) : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = (ℓ.1 : ℕ) ^ 2)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀)

    (Xq : Scheme.{0}) (πXq : Xq ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (πq : M ⟶ Xq) (hπqX : πq ≫ πXq = πM)
    (hπq : ∀ g : G, (ρ g).hom ≫ πq = πq)
    (hintq : IsIntegralHom πq) (haffq : IsAffineHom πq) (hsurjq : Function.Surjective πq.base)
    (horbitq : ∀ x x' : M, πq.base x = πq.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hsecq : ∀ V : Xq.Opens, Function.Injective (πq.app V))
    (hinvq : ∀ V : Xq.Opens, Set.range (πq.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (πq ⁻¹ᵁ V) (πq ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπq g]) s = s})
    (hopenq : ∀ W : M.Opens, IsAffineOpen W → (∀ g : G, (ρ g).hom ⁻¹ᵁ W = W) → ∃ V : Xq.Opens, IsAffineOpen V ∧ πq ⁻¹ᵁ V = W)
    (hcatq : ∀ (T : Scheme.{0}) (f : M ⟶ T), (∀ g : G, (ρ g).hom ≫ f = f) → ∃! f' : Xq ⟶ T, πq ≫ f' = f)
    (ptq : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πXq)
    (hXq : IsCoarseModuli Λ N Xq πXq ptq)
    (hptq : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithFullLevel Λ N m S), (ptq S s u.1).1 = (ptF S s u).1 ≫ πq)

    (gX : Xq ⟶ CategoryTheory.Limits.pullback πX sbar) (hgXiso : IsIso gX)
    (hgXπ : gX ≫ CategoryTheory.Limits.pullback.snd πX sbar = πXq)
    (hgXpt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (E' : FakeEllipticCurve Λ N S),
      (ptq S s E').1 ≫ gX ≫ CategoryTheory.Limits.pullback.fst πX sbar = (pt S (s ≫ sbar) E').1)

    (XH : Scheme.{0}) (πXH : XH ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (πH : M ⟶ XH) (hπHX : πH ≫ πXH = πM)
    (hπH : ∀ h : H, (ρ h).hom ≫ πH = πH)
    (hintH : IsIntegralHom πH) (haffH : IsAffineHom πH) (hsurjH : Function.Surjective πH.base)
    (horbitH : ∀ x x' : M, πH.base x = πH.base x' ↔ ∃ h : H, (ρ h).hom.base x = x')
    (hsecH : ∀ V : XH.Opens, Function.Injective (πH.app V))
    (hinvH : ∀ V : XH.Opens, Set.range (πH.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (πH ⁻¹ᵁ V) (πH ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπH h]) s = s})
    (hopenH : ∀ W : M.Opens, IsAffineOpen W → (∀ h : H, (ρ h).hom ⁻¹ᵁ W = W) → ∃ V : XH.Opens, IsAffineOpen V ∧ πH ⁻¹ᵁ V = W)
    (hcatH : ∀ (T : Scheme.{0}) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : XH ⟶ T, πH ≫ f' = f)
    (dH : XH ⟶ Xq) (hdH : πH ≫ dH = πq)

    (U : XH.Opens)
    (ptU : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (U.ι ≫ πXH))
    (hUclosed : IsClosed (U : Set XH))
    (hU : IsCoarseModuliT Λ N (ℓ.1 : ℕ) (U : Scheme.{0}) (U.ι ≫ πXH) ptU)
    (hUptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithFullLevel Λ N m S) (K' : u.1.ExtraLevel (ℓ.1 : ℕ)),
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) u.1.f),
        FactorsThrough K'.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (u.1.act x) (u.1.act_over x)
              (nsmulPt u.1.L (geomPoint k sk) (m / (ℓ.1 : ℕ)) (FakeEllipticCurve.sectionAt u.2.P k sk)) = Q) →
      (ptU S s ⟨u.1, K'⟩).1 ≫ U.ι = (ptF S s u).1 ≫ πH)
    (hUd : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (v : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptU S s v).1 ≫ U.ι ≫ dH = (ptq S s v.1).1)
    (hUtop : ¬ (ℓ.1 : ℕ) ∣ N → U = ⊤)
    (gU : (U : Scheme.{0}) ⟶ Y) (hgUiso : IsIso gU) (hgUπ : gU ≫ πY = U.ι ≫ πXH)
    (hgUpt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT S s u).1 = (ptU S s u).1 ≫ gU)

    (P : E.FullLevel m) (i₀ : Fin n)
    (hK₀ : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : (AlgebraicClosure ℚ) →+* k')
      (Q : SchemeHomOver (geomPoint k' sk) E.f),
      FactorsThrough (K i₀).levK Q ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
          pushPt (E.act x) (E.act_over x)
            (nsmulPt E.L (geomPoint k' sk) (m / (ℓ.1 : ℕ)) (FakeEllipticCurve.sectionAt P.P k' sk)) = Q)
    (hpt₀ : (ptT _ (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) (⟨E, K i₀⟩ : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ))).1 =
      (𝔐ℓ.pointEquivPlace.symm R).1 ≫ eℓ) :
    ∃ (Mf : Type) (_ : Field Mf) (_ : Algebra (AlgebraicClosure ℚ) Mf) (_ : Algebra Fbar Mf) (_ : Algebra (𝕋.F ℓ) Mf)
      (_ : IsScalarTower (AlgebraicClosure ℚ) Fbar Mf) (_ : IsScalarTower (AlgebraicClosure ℚ) (𝕋.F ℓ) Mf)
      (_ : FiniteDimensional Fbar Mf) (_ : FiniteDimensional (𝕋.F ℓ) Mf) (_ : IsGalois Fbar Mf)
      (c : Place (AlgebraicClosure ℚ) Mf),
      (∀ x : Fbar, algebraMap Fbar Mf x = algebraMap (𝕋.F ℓ) Mf (𝕋.φ (ℓ, 0) x)) ∧
      c.restrict (𝕋.F ℓ) = R ∧
      Nat.card {σ : Mf ≃ₐ[Fbar] Mf // SemilinearAut.ofAlgAut (σ.restrictScalars (AlgebraicClosure ℚ)) • c = c} *
          Nat.card {g : G // g ∈ H ∧
            (ptF (AlgebraicClosure ℚ) (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ⟨E, P⟩).1 ≫ (ρ g).hom =
              (ptF (AlgebraicClosure ℚ) (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ⟨E, P⟩).1} =
        Nat.card {σ : Mf ≃ₐ[𝕋.F ℓ] Mf // SemilinearAut.ofAlgAut (σ.restrictScalars (AlgebraicClosure ℚ)) • c = c} *
          Nat.card {g : G //
            (ptF (AlgebraicClosure ℚ) (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ⟨E, P⟩).1 ≫ (ρ g).hom =
              (ptF (AlgebraicClosure ℚ) (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ⟨E, P⟩).1} := by sorry
