-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_perm_quotVert_quotEdge_realisation_independent_of_descentIntertwining_zero_one
-- name    : CerednikDrinfeld.exists_perm_quotVert_quotEdge_realisation_independent_of_descentIntertwining_zero_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/2ba3c3ef-7545-52e2-8041-2f1d00cbfdbe
-- title:
--   Realisation-independent permutation actions on Bruhat–Tits tree quotients
-- statement:
--   Throughout, $B=\mathbb H[\mathbb Q,a_1,b_1]$ for rationals $a_1,b_1$, and $N,q,q'$ are natural numbers with $N$ non-zero and squarefree (`hN`), $q$ and $q'$ prime, $q\nmid N$, $q'\nmid N$, $q'\neq q$ and $q,q'\ge 5$.
--
--   **Quaternionic data.** The hypothesis `hdef₁` asserts $a_1<0$, $b_1<0$, and that for a finite place $v$ of $\mathbb Q$ every non-zero element of $B\otimes_{\mathbb Q}\mathbb Q_v$ is a unit exactly when $q'$ lies in $v$; so $B$ is definite and ramified precisely at $q'$ among the finite places. $\Lambda_1$ is a $\mathbb Z$-submodule of $B$ which is a maximal order (an order — containing $1$, closed under multiplication, spanning $B$ over $\mathbb Q$, finitely generated — maximal among orders), $R_1$ is an Eichler order of index $N$ (an intersection of two maximal orders whose relative index in the first is $N$) contained in $\Lambda_1$. The finite-adelic unit $n_1$ lies in `primeHeckeSet R₁ q`: $n_1$ lies in the finite-adelic box of $R_1$, $q\,n_1^{-1}$ lies in that box, while $n_1^{-1}$ and $q^{-1}n_1$ do not. Writing $S_1=$ `meetOrder R₁ n₁` $=R_1\cap n_1R_1n_1^{-1}$ (conjugation by the finite idele $n_1$), the hypotheses require $S_1$ to be an Eichler order of index $Nq$ (`hS₁`), $n_1$ to normalise $S_1$ (`hnorm₁`), and the shift $x\mapsto [\,x\cdot n_1\,]$ on the class set of the finite-idelic stabiliser of $S_1$ to be an involution (`hsq₁`). The class sets of the stabilisers of $S_1$ and of $R_1$ are finite. Finally `hlaws₁` is `ClassSetHeckeLaws N q Λ₁ R₁ n₁`: the edge Hecke matrices commute pairwise, the vertex Hecke matrices commute pairwise, for primes $\ell\neq q$ the two degeneracy pushforwards intertwine edge and vertex Hecke operators, and each edge Hecke operator preserves the common kernel of the two degeneracy pushforwards.
--
--   **The place above $q$ and the local data.** $A_2$ is a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A_2$ (`hA₂`), and the decomposition subgroup of $A_2$ over $\mathbb Q$ acts isometrically for the valuation of $A_2$. Put $K_0=$ [`ValuationSubring.ratClosure A₂`](def/ValuationSubring_CompletionRatClosure.html#L13), the topological closure of the prime subfield inside the completion of $\overline{\mathbb Q}$ for that valuation. $v_2$ is the height-one prime of $\mathbb Z$ containing $q$ (`hv₂`). $\iota_2\colon B\to M_2(K_0)$ is an injective $\mathbb Q$-algebra map, and $\rho_2\colon B^\times\to\mathrm{PGL}_2(K_0)$ sends $x$ to the class of $\iota_2(x)$ (`hρ₂`). $\varpi_2$ is a pseudo-uniformiser of $K_0$ in the completion (its image has valuation strictly between $0$ and $1$, together with the scaling condition) whose image equals $q$ (`hϖ₂`), and the ring `HolRingOf ϖ₂ ρ₂` of functions on the $p$-adic upper half plane holomorphic on every affinoid is assumed to be a domain. $R_0$ is a discrete valuation ring which is a domain, with $K_0$ as fraction field and finite residue field, and `hR₀` identifies the image of $R_0$ in $K_0$ with the elements of valuation at most $1$. $\mathrm{dIso}_2$ is a homomorphism from the decomposition subgroup to the isometric automorphisms of the completion over $K_0$, whose underlying ring equivalence is the given action (`hdIso₂`).
--
--   **The function-field tower.** $F_N$ is a field over $\overline{\mathbb Q}$ which is a curve over $\overline{\mathbb Q}$ (principal divisors exist, residue fields at places are finite over $\overline{\mathbb Q}$, and the module of Kähler differentials is free of rank one) and essentially of finite type, and $\mathbb T$ is tower data `HeckeTower.TowerData q q' FN`: fields $\mathbb T.F\,\ell$ for the primes $\ell\notin\{q,q'\}$, each a curve over $\overline{\mathbb Q}$ and essentially of finite type, together with $\overline{\mathbb Q}$-algebra maps from $F_N$ along the arrows which are finite and integral. The storeys of the tower are indexed by `HeckeTower.Obj q q'` $=$ `Option (AwayPrime q q')`, the storey at `none` being $F_N$. The hypothesis `hfg` provides in each storey a transcendental element $x$ over $\overline{\mathbb Q}$ with the storey finite-dimensional over $\overline{\mathbb Q}(x)$. The homomorphisms $\mathrm{gal}_N$ and $\mathrm{gal}_T(\ell)$ give semilinear actions of the decomposition subgroup on $F_N$ and on each $\mathbb T.F\,\ell$, whose base parts are the given automorphisms of $\overline{\mathbb Q}$ (`hgalN`, `hgalT`); $W$ and $WT(\ell)$ are pairs of semilinear automorphisms of $F_N$ and of $\mathbb T.F\,\ell$. $\chi_2$ is a character of the decomposition subgroup with values in $\mathrm{Multiplicative}(\mathbb Z/2)$, and $\iota_{M,2}(j)$ are ring embeddings of the storeys into the fraction field of `HolRingOf ϖ₂ ρ₂`. The hypothesis `hI` is the predicate [`CerednikDrinfeld.DescentIntertwining`](def/CerednikDrinfeld_DescentIntertwining_v2.html#L17) at $r=q$ and the index pair $0,1$ of `Fin 2`, for the data $A_2,\rho_2,\varpi_2,\Gamma_2,w_2,\bar w_2,s_2,\mathrm{dIso}_2,F_N,\mathbb T,\mathrm{gal}_N,\mathrm{gal}_T,W,WT,\chi_2,\iota_{M,2}$; among its requirements are that $\chi_2$ be trivial on the inertia subgroup at $A_2$, non-trivial at every Frobenius element for $q$, that $\chi_2(\tau)=1$ hold exactly when $\tau$ fixes every element $x$ of the residue field of $A_2$ with $x^{q^2}=x$, and that each $\iota_{M,2}(j)$ carry the constants $\overline{\mathbb Q}$ to the constants of the completion.
--
--   **Level groups and exchanging elements.** For each prime $\ell\notin\{q,q'\}$ there are $s_2(\ell)\in B^\times$ and a finite-adelic unit $sf_2(\ell)$; `hs₂` requires, for each $\ell$: the component of $sf_2(\ell)$ at each finite place $u$ not containing $q$ is $s_2(\ell)\otimes 1$; the component at each place containing $q$ is $1$; the product of the diagonal idele of the scalar $\ell$ with $sf_2(\ell)^{-1}$ lies in `levelHeckeUSet Λ₁ S₁ ℓ` if $\ell\mid N$ and in `primeHeckeSet S₁ ℓ` otherwise (the former consisting of those $h$ in the latter with $h S_1 h^{-1}\neq S_1$ and $S_1\not\le h\Lambda_1h^{-1}$); and $\mathrm{nrd}(s_2(\ell))=\ell$. The groups $\Gamma_2(j)\le B^\times$ are pinned by `hΓ₂0`, which says that $\Gamma_2(\text{none})$ consists of the units lying in `awayUnits R₁ v₂` (units whose local image at every place $w\neq v_2$ lies in the subgroup generated by the local box units of $R_1$ at $w$) whose reduced norm has even $q$-adic valuation, and by `hΓ₂ℓ`, which sets $\Gamma_2(\mathrm{some}\ \ell)=\Gamma_2(\text{none})\cap s_2(\ell)\Gamma_2(\text{none})s_2(\ell)^{-1}$. The elements $w_2(j),\bar w_2(j)\in B^\times$ satisfy: `hw₂`, that $w_2(\text{none})$ lies in `awayUnits R₁ v₂` with reduced norm $q$, and $w_2(\mathrm{some}\ \ell)$ lies in `awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂` with reduced norm $q$; and `hwbar₂`, that for each storey $\bar w_2(j)$ has reduced norm $q'$, its local image at every place $u\neq v_2$ not containing $q'$ is a unit of the local box of the relevant order ($R_1$ for $j=\text{none}$, $R_1\cap sf_2(\ell)R_1sf_2(\ell)^{-1}$ for $j=\mathrm{some}\ \ell$), and conjugation by its local image at every $u\neq v_2$ preserves the local box of that order and the local box of $\Lambda_1$, in both directions.
--
--   **The symmetry group.** $S_2$ is a group with a homomorphism $\mathrm{scalar}_2$ to the decomposition subgroup and a section $\iota_{S,2}$ of it (`hιS₂`), distinguished elements $\sigma_{0},\sigma_{1}$, characters $\chi_{S,2}$ to $\mathrm{Multiplicative}(\mathbb Z/2)$ and $\mathrm{sgn}_2$ to $\mathbb Z^\times$, and for each storey $j$ a homomorphism $\mathrm{galFC}_2(j)$ from $S_2$ to the semilinear automorphisms, over the completion, of the Mumford field $\mathcal M_j=$ `invariantFieldOf … (Γ₂ j)`, the subfield of the fraction field of `HolRingOf ϖ₂ ρ₂` fixed by every element of $\Gamma_2(j)$. The group-theoretic hypotheses are: `hgen₂`, every $\sigma\in S_2$ is of the form $\iota_{S,2}(\tau)\sigma_0^{u}\sigma_1^{v}$; `hrel₂`, that $\sigma_0$ and $\sigma_1$ are commuting involutions each commuting with all $\iota_{S,2}(\tau)$; and `huniv₂`, the corresponding universal property — for every group $H$, homomorphism $f$ from the decomposition subgroup and commuting involutions $h_0,h_1$ of $H$ commuting with the image of $f$, there is a homomorphism $S_2\to H$ carrying $\iota_{S,2}(\tau)$ to $f(\tau)$, $\sigma_0$ to $h_0$ and $\sigma_1$ to $h_1$. The characters satisfy `hχS₂` ($\chi_{S,2}\circ\iota_{S,2}=\chi_2$, $\chi_{S,2}(\sigma_0)\neq1$, $\chi_{S,2}(\sigma_1)=1$) and `hsgnS₂` ($\mathrm{sgn}_2(\iota_{S,2}(\tau))=1$ when $\chi_{S,2}(\iota_{S,2}(\tau))=1$, $\mathrm{sgn}_2(\iota_{S,2}(\tau))=\mathrm{sgn}_2(\sigma_0)$ otherwise, $\mathrm{sgn}_2(\sigma_0)=-1$, $\mathrm{sgn}_2(\sigma_1)=1$). The action pins are: `hbase₂`, the base part of $\mathrm{galFC}_2(j)(\sigma)$ on the completion is $\mathrm{dIso}_2(\mathrm{scalar}_2(\sigma))$; `hactD₂`, for $\tau$ in the decomposition subgroup $\mathrm{galFC}_2(j)(\iota_{S,2}(\tau))$ acts on $\mathcal M_j$ by $y\mapsto u\cdot\big(\text{coefficientwise }\mathrm{dIso}_2(\tau)\big)(y)$ with $u=1$ if $\chi_2(\tau)=1$ and $u=w_2(j)$ otherwise; `hact₀₂`, $\mathrm{galFC}_2(j)(\sigma_0)$ acts by $y\mapsto w_2(j)\cdot y$; and `hact₁₂`, $\mathrm{galFC}_2(j)(\sigma_1)$ acts by $y\mapsto \bar w_2(j)\cdot y$.
--
--   **Conclusion.** Let $\mathcal T=$ `BruhatTits.tree R₀ K₀` be the graph on the homothety classes of full $R_0$-lattices in $K_0^2$ with adjacency given by the adjacency relation of lattices, and for a storey $j$ let $G_j=\rho_2(\Gamma_2(j))\le\mathrm{PGL}_2(K_0)$. Then there exist families of homomorphisms
--   $$\pi_V(j)\colon S_2\to \mathrm{Sym}\big(G_j\backslash\mathrm{Vert}(\mathcal T)\big),\qquad \pi_E(j)\colon S_2\to\mathrm{Sym}\big(\{e\in G_j\backslash\mathrm{Dart}(\mathcal T)\ :\ \text{the source of }e\text{'s chosen representative has vertex type }0\}\big),$$
--   where the vertex type of $w$ is the distance from the standard vertex of $\mathcal T$ reduced modulo $2$, such that all of the following hold.
--
--   First, for every storey $j$ and every vertex $v$, $\pi_V(j)(\sigma_0)$ sends the $G_j$-orbit of $v$ to the orbit of $\rho_2(w_2(j))\cdot v$. Second, $\pi_V(j)(\sigma_1)$ sends the orbit of $v$ to the orbit of $\rho_2(\bar w_2(j))\cdot v$. Third, for every $j$ and every $e$ in the above subtype, the dart-orbit underlying $\pi_E(j)(\sigma_0)(e)$ is the orbit of the reversal of $\rho_2(w_2(j))$ applied to the chosen representative dart of $e$. Fourth, the dart-orbit underlying $\pi_E(j)(\sigma_1)(e)$ is the orbit of $\rho_2(\bar w_2(j))$ applied to that representative dart, without reversal. Fifth, for every $j$ and every $\tau$ in the decomposition subgroup with $\chi_2(\tau)=1$, both $\pi_V(j)(\iota_{S,2}(\tau))$ and $\pi_E(j)(\iota_{S,2}(\tau))$ are the identity permutations. Sixth, for every $j$ and every $\tau$ with $\chi_2(\tau)\neq1$, $\pi_V(j)(\iota_{S,2}(\tau))=\pi_V(j)(\sigma_0)$ and $\pi_E(j)(\iota_{S,2}(\tau))=\pi_E(j)(\sigma_0)$.
--
--   Seventh, the realisation-independence clause: for every storey $j$, every $\sigma\in S_2$, every $n\in B^\times$ normalising $\Gamma_2(j)$ and every isometric automorphism $t$ of the completion over $K_0$ such that $\mathrm{galFC}_2(j)(\sigma)$ acts on $\mathcal M_j$ by $y\mapsto n\cdot\big(\text{the fraction-field map induced by the coefficientwise action of }t\big)(y)$, one has: for every vertex $v$, $\pi_V(j)(\sigma)$ sends the orbit of $v$ to the orbit of $\rho_2(n)\cdot v$; and for every $e$ in the subtype of dart-orbits of source type $0$, if $\rho_2(n)$ preserves vertex types with respect to the standard vertex then $\mathrm{sgn}_2(\sigma)=1$ and the dart-orbit underlying $\pi_E(j)(\sigma)(e)$ is the orbit of $\rho_2(n)$ applied to the chosen representative dart of $e$, whereas if $\rho_2(n)$ does not preserve vertex types then $\mathrm{sgn}_2(\sigma)=-1$ and that dart-orbit is the orbit of the reversal of $\rho_2(n)$ applied to the chosen representative dart.
--
--   This is the Mumford-side bookkeeping of the Čerednik–Drinfeld description of the special fibre: the Frobenius-and-Atkin–Lehner symmetry group acts on the quotient of the Bruhat–Tits tree by the level group, by the orbit maps of the exchanging elements $w_2(j)$ and $\bar w_2(j)$, with a sign recording whether the relevant projective element preserves the bipartition, and the resulting permutations depend only on the symmetry, not on the element of $B^\times$ chosen to realise it on the Mumford function field. It feeds the presentation of the quotient graph in terms of class sets and Hecke operators used by [`CerednikDrinfeld.exists_quotientPresentation_classSet_hecke_of_descentIntertwining_zero_one`](thm.html#CerednikDrinfeld.exists_quotientPresentation_classSet_hecke_of_descentIntertwining_zero_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_perm_quotVert_quotEdge_realisation_independent_of_descentIntertwining_zero_one.lean

import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

theorem CerednikDrinfeld.exists_perm_quotVert_quotEdge_realisation_independent_of_descentIntertwining_zero_one

    {a₁ b₁ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₁ : IsDefiniteRamifiedExactlyAt a₁ b₁ q')
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ q)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * q))
    (hnorm₁ : Submodule.conjByFiniteIdele (meetOrder R₁ n₁) n₁ = meetOrder R₁ n₁)
    (hsq₁ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)),
      classSetShift _ n₁ (classSetShift _ n₁ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    (hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁)

    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)

    (FN : Type) [Field FN] [Algebra (AlgebraicClosure ℚ) FN] [IsCurveOver (AlgebraicClosure ℚ) FN]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) FN]
    (𝕋 : HeckeTower.TowerData q q' FN)
    (hfg : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))
    (galN : ↥(A₂.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) FN)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A₂.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (hgalN : ∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galN τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (hgalT : ∀ ℓ (τ : ↥(A₂.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galT ℓ τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) FN) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

    [hiso₂ : Fact (A₂.DecompositionIsometric ℚ)]
    (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : ((q : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal)

    (ι₂ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) (hι₂ : Function.Injective ι₂)
    (ρ₂ : (ℍ[ℚ, a₁, b₁])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₂)))
    (hρ₂ : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, ρ₂ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) x))

    (ϖ₂ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
    (hϖ₂ : algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion ϖ₂.ϖ = ((q : AlgebraicClosure ℚ) : A₂.valuation.Completion))
    [hdom₂ : IsDomain (Omega.HolRingOf ϖ₂ ρ₂)]

    (s₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₂ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₂ ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₂ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s₂ ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₂ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓ₂0 : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ₂ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁]))))
    (hΓ₂ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₂ (some ℓ) = Γ₂ none ⊓ (Γ₂ none).map (MulAut.conj (s₂ ℓ)).toMonoidHom)

    (w₂ wbar₂ : HeckeTower.Obj q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (hw₂ : (w₂ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ nrd (w₂ none : ℍ[ℚ, a₁, b₁]) = (q : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₂ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂ ∧ nrd (w₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (q : ℚ))
    (hwbar₂ :
      (nrd (wbar₂ none : ℍ[ℚ, a₁, b₁]) = (q' : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₂ none) ∈ Submodule.localBoxUnits R₁ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox R₁ u ↔
            x ∈ Submodule.localBox R₁ u) ∧
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
            x ∈ Submodule.localBox Λ₁ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (q' : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₂ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₁ (sf₂ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
              x ∈ Submodule.localBox Λ₁ u))))

    (dIso₂ : ↥(A₂.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
    (hdIso₂ : ∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (x : A₂.valuation.Completion), (dIso₂ τ).toRingEquiv x = τ • x)

    (χ₂ : ↥(A₂.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (ιM₂ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂))
    (hI : CerednikDrinfeld.DescentIntertwining q (0 : Fin 2) (1 : Fin 2) A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂
      FN 𝕋 galN galT W WT χ₂ ιM₂)

    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Algebra R₀ ↥(ValuationSubring.ratClosure A₂)] [IsFractionRing R₀ ↥(ValuationSubring.ratClosure A₂)] [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : ↥(ValuationSubring.ratClosure A₂), x ∈ Set.range (algebraMap R₀ ↥(ValuationSubring.ratClosure A₂)) ↔ Valued.v (algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion x) ≤ 1)

    (S₂ : Type) [Group S₂] (scalar₂ : S₂ →* ↥(A₂.decompositionSubgroup ℚ))
    (ιS₂ : ↥(A₂.decompositionSubgroup ℚ) →* S₂) (hιS₂ : ∀ τ, scalar₂ (ιS₂ τ) = τ)
    (σ₀₂ σ₁₂ : S₂) (χS₂ : S₂ →* Multiplicative (ZMod 2)) (sgn₂ : S₂ →* ℤˣ)
    (galFC₂ : ∀ j : HeckeTower.Obj q q', S₂ →* SemilinearAut A₂.valuation.Completion ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j)))

    (hgen₂ : ∀ σ : S₂, ∃ (τ : ↥(A₂.decompositionSubgroup ℚ)) (u v : ℕ), σ = ιS₂ τ * σ₀₂ ^ u * σ₁₂ ^ v)
    (hrel₂ : σ₀₂ * σ₀₂ = 1 ∧ σ₁₂ * σ₁₂ = 1 ∧ σ₀₂ * σ₁₂ = σ₁₂ * σ₀₂ ∧
      (∀ τ, ιS₂ τ * σ₀₂ = σ₀₂ * ιS₂ τ) ∧ (∀ τ, ιS₂ τ * σ₁₂ = σ₁₂ * ιS₂ τ))
    (huniv₂ : ∀ (H : Type) [Group H] (f : ↥(A₂.decompositionSubgroup ℚ) →* H) (h₀ h₁ : H),
      h₀ * h₀ = 1 → h₁ * h₁ = 1 → h₀ * h₁ = h₁ * h₀ → (∀ τ, f τ * h₀ = h₀ * f τ) → (∀ τ, f τ * h₁ = h₁ * f τ) →
      ∃ F : S₂ →* H, (∀ τ, F (ιS₂ τ) = f τ) ∧ F σ₀₂ = h₀ ∧ F σ₁₂ = h₁)

    (hχS₂ : (∀ τ, χS₂ (ιS₂ τ) = χ₂ τ) ∧ χS₂ σ₀₂ ≠ 1 ∧ χS₂ σ₁₂ = 1)
    (hsgnS₂ : (∀ τ, χS₂ (ιS₂ τ) = 1 → sgn₂ (ιS₂ τ) = 1) ∧ (∀ τ, χS₂ (ιS₂ τ) ≠ 1 → sgn₂ (ιS₂ τ) = sgn₂ σ₀₂) ∧
      sgn₂ σ₀₂ = -1 ∧ sgn₂ σ₁₂ = 1)

    (hbase₂ : ∀ j (σ : S₂) (c : A₂.valuation.Completion), SemilinearAut.baseAut (galFC₂ j σ) c = (dIso₂ (scalar₂ σ)).toRingEquiv c)
    (hactD₂ : ∀ j (τ : ↥(A₂.decompositionSubgroup ℚ)) (y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))),
      ((galFC₂ j (ιS₂ τ) • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
        (if χ₂ τ = 1 then (1 : (ℍ[ℚ, a₁, b₁])ˣ) else w₂ j) • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ (dIso₂ τ)) (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)))
    (hact₀₂ : ∀ j (y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))), ((galFC₂ j σ₀₂ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = (w₂ j) • (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)))
    (hact₁₂ : ∀ j (y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))), ((galFC₂ j σ₁₂ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = (wbar₂ j) • (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) :
    ∃ (πV : ∀ j : HeckeTower.Obj q q', S₂ →* Equiv.Perm (Mumford.QuotVert ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))))
      (πE : ∀ j : HeckeTower.Obj q q', S₂ →* Equiv.Perm {e : Mumford.QuotEdge ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) e.out.fst = 0}),

      (∀ j (v : LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂)), πV j σ₀₂ (Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) v) =
        Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) (ρ₂ (w₂ j) • v)) ∧
      (∀ j (v : LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂)), πV j σ₁₂ (Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) v) =
        Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) (ρ₂ (wbar₂ j) • v)) ∧
      (∀ j (e : {e : Mumford.QuotEdge ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) e.out.fst = 0}), ((πE j σ₀₂ e).1 : Mumford.QuotEdge ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂))) =
        Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)).Dart) (ρ₂ (w₂ j) • e.1.out).symm) ∧
      (∀ j (e : {e : Mumford.QuotEdge ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) e.out.fst = 0}), ((πE j σ₁₂ e).1 : Mumford.QuotEdge ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂))) =
        Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)).Dart) (ρ₂ (wbar₂ j) • e.1.out)) ∧
      (∀ j (τ : ↥(A₂.decompositionSubgroup ℚ)), χ₂ τ = 1 → πV j (ιS₂ τ) = 1 ∧ πE j (ιS₂ τ) = 1) ∧
      (∀ j (τ : ↥(A₂.decompositionSubgroup ℚ)), χ₂ τ ≠ 1 → πV j (ιS₂ τ) = πV j σ₀₂ ∧ πE j (ιS₂ τ) = πE j σ₀₂) ∧

      (∀ j (σ : S₂) (n : (ℍ[ℚ, a₁, b₁])ˣ) (t : Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion),
        n ∈ Subgroup.normalizer ((Γ₂ j : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) : Set (ℍ[ℚ, a₁, b₁])ˣ) →
        (∀ y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j)), ((galFC₂ j σ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ t) (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) →
        (∀ v : (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂)), πV j σ ((Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) v)) = (Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) (ρ₂ n • v))) ∧
        (∀ e : {e : Mumford.QuotEdge ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) e.out.fst = 0},
          (ρ₂ n ∈ Mumford.typePreserving PGL(2, ↥(ValuationSubring.ratClosure A₂)) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) → sgn₂ σ = 1 ∧ (πE j σ e).1 = Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)).Dart) (ρ₂ n • e.1.out)) ∧
          (ρ₂ n ∉ Mumford.typePreserving PGL(2, ↥(ValuationSubring.ratClosure A₂)) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) → sgn₂ σ = -1 ∧ (πE j σ e).1 = Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)).Dart) (ρ₂ n • e.1.out).symm))) := by sorry
