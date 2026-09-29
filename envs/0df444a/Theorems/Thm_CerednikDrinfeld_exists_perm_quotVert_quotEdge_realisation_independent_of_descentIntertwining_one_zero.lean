-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_perm_quotVert_quotEdge_realisation_independent_of_descentIntertwining_one_zero
-- name    : CerednikDrinfeld.exists_perm_quotVert_quotEdge_realisation_independent_of_descentIntertwining_one_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/d1674018-c5fc-5098-8d95-047774e7fc23
-- title:
--   Realisation-independent permutation actions on quotients of the Bruhat–Tits tree
-- statement:
--   Arithmetic data. Fixed are rationals $a_2,b_2$ and naturals $N,q,q'$ with $N$ nonzero and squarefree, $q$ and $q'$ prime, $q\nmid N$, $q'\nmid N$, $q'\neq q$ and $5\le q$, $5\le q'$. The hypothesis `hdef₂` requires $a_2<0$, $b_2<0$ and that, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the algebra $\mathbb H[\mathbb Q,a_2,b_2]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $q\in v$; thus the quaternion algebra is definite and ramified precisely at $q$. Two $\mathbb Z$-submodules $\Lambda_2,R_2$ of $\mathbb H[\mathbb Q,a_2,b_2]$ are given with $\Lambda_2$ a maximal order, $R_2$ an Eichler order of level $N$ (an intersection of two maximal orders of relative index $N$ in one of them) and $R_2\le\Lambda_2$. A finite-idelic unit $n_2$ of $\mathbb H[\mathbb Q,a_2,b_2]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{\mathrm{fin}}$ lies in `primeHeckeSet R₂ q'`, that is, $n_2$ and $q'n_2^{-1}$ lie in the adelic box of $R_2$ while $n_2^{-1}$ and $q'^{-1}n_2$ do not; `hS₂` requires $\mathrm{meetOrder}\,R_2\,n_2=R_2\cap n_2R_2n_2^{-1}$ to be an Eichler order of level $Nq'$, `hnorm₂` that $n_2$ normalises this order, and `hsq₂` that the shift by $n_2$ on the class set of its finite-idelic stabiliser is an involution; the two class sets occurring (for $\mathrm{meetOrder}\,R_2\,n_2$ and for $R_2$) are assumed finite. The hypothesis `hlaws₂` is `ClassSetHeckeLaws N q' Λ₂ R₂ n₂`: the edge Hecke matrices commute pairwise, the vertex Hecke matrices commute pairwise, for every prime $\ell\neq q'$ the two degeneracy pushforwards intertwine the edge and vertex Hecke matrices, and for every prime the edge Hecke matrices preserve the subspace where both degeneracy pushforwards vanish.
--
--   The place over $q'$ and the tower of curves. A valuation subring $A_1$ of $\overline{\mathbb Q}$ is given with $q'$ a non-unit of $A_1$, and its decomposition subgroup over $\mathbb Q$ is assumed to act isometrically for the valuation of $A_1$. A field $F_N$ is an $\overline{\mathbb Q}$-algebra which is a curve over $\overline{\mathbb Q}$ in the sense of `IsCurveOver` (principal divisors of degree zero exist for all nonzero functions, all residue fields of places are finite over $\overline{\mathbb Q}$, and $\Omega_{F_N/\overline{\mathbb Q}}$ is free of rank one) and is essentially of finite type; $\mathbb T$ is a `HeckeTower.TowerData q q' FN`, i.e. a family of curves $\mathbb T.F\,\ell$ over $\overline{\mathbb Q}$ indexed by the primes $\ell\notin\{q,q'\}$, together with finite integral $\overline{\mathbb Q}$-algebra maps $F_N\to\mathbb T.F\,\alpha_1$ for each arrow $\alpha$ of the tower. The hypothesis `hfg` requires each field $\mathbb T.\mathrm{objField}\,j$ (with $j$ ranging over $\mathrm{Obj}=\mathrm{Option}$ of the away-primes, the base being $j=\mathtt{none}$) to contain a transcendental element over which it is finite. Homomorphisms `galN` and `galT ℓ` from the decomposition subgroup of $A_1$ to the semilinear automorphism groups of $F_N$ and of each $\mathbb T.F\,\ell$ over $\overline{\mathbb Q}$ are given, whose base automorphism is, by `hgalN` and `hgalT`, the given element $\tau$ of the decomposition subgroup itself; $W$ and $WT\,\ell$ are pairs of semilinear automorphisms of $F_N$ and of $\mathbb T.F\,\ell$ indexed by $\mathrm{Fin}\,2$.
--
--   The analytic data. A height-one prime $v_1$ of $\mathcal O_{\mathbb Q}$ contains $q'$. Write $K_0=\mathrm{ratClosure}\,A_1$ for the topological closure of the prime subfield in the completion $K=A_1.\mathrm{valuation.Completion}$. An injective $\mathbb Q$-algebra map $\iota_1:\mathbb H[\mathbb Q,a_2,b_2]\to M_2(K_0)$ is given, and $\rho_1:\mathbb H[\mathbb Q,a_2,b_2]^\times\to\mathrm{PGL}_2(K_0)$ is, by `hρ₁`, the projective representation induced by $\iota_1$. A pseudo-uniformizer $\varpi_1$ of $K_0$ in $K$ is given whose image in $K$ is $q'$, and the ring $\mathrm{HolRingOf}\,\varpi_1\,\rho_1$ of functions on the $q'$-adic upper half plane that are holomorphic on every affinoid of the exhaustion is assumed to be a domain. A discrete valuation ring $R_0$ with finite residue field is given with $K_0$ as its fraction field, and `hR₀` identifies its image in $K_0$ with the elements of valuation at most $1$; its Bruhat–Tits tree has as vertices the homothety classes of full lattices in $K_0^2$, adjacency being given by `VertRel`.
--
--   For each away-prime $\ell$ a unit $s_1\ell$ of the quaternion algebra and a finite-idelic unit $sf_1\ell$ are given; `hs₁` requires, for each $\ell$: the component of $sf_1\ell$ at each prime not containing $q'$ is $s_1\ell\otimes1$; its component at each prime containing $q'$ is $1$; the product of the diagonal image of the scalar $\ell$ with $(sf_1\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ (meetOrder R₂ n₂) ℓ` if $\ell\mid N$ and in `primeHeckeSet (meetOrder R₂ n₂) ℓ` otherwise; and $\mathrm{nrd}(s_1\ell)=\ell$.
--
--   Level groups and involutions. Subgroups $\Gamma_1 j\le\mathbb H[\mathbb Q,a_2,b_2]^\times$ are given with $\Gamma_1(\mathtt{none})$ characterised by `hΓ₁0` as the units lying in `awayUnits R₂ v₁` (units whose image in $\mathbb H\otimes\mathbb Q_w$ lies in the subgroup generated by the local box units of $R_2$ at $w$, for every $w\neq v_1$) and whose reduced norm has even $q'$-adic valuation, while `hΓ₁ℓ` sets $\Gamma_1(\mathtt{some }\ell)=\Gamma_1(\mathtt{none})\cap s_1\ell\,\Gamma_1(\mathtt{none})\,s_1\ell^{-1}$. Units $w_1 j$ and $\bar w_1 j$ are given: `hw₁` requires $w_1(\mathtt{none})\in\mathrm{awayUnits}\,R_2\,v_1$ with $\mathrm{nrd}(w_1(\mathtt{none}))=q'$, and $w_1(\mathtt{some }\ell)\in\mathrm{awayUnits}(\mathrm{meetOrder}\,R_2\,(sf_1\ell))\,v_1$ with reduced norm $q'$; `hwbar₁` requires, both for $j=\mathtt{none}$ (with the order $R_2$) and for $j=\mathtt{some }\ell$ (with the order $\mathrm{meetOrder}\,R_2\,(sf_1\ell))$, that $\mathrm{nrd}(\bar w_1 j)=q$, that the local image of $\bar w_1 j$ at each $u\neq v_1$ not containing $q$ lies in the local box units of that order, and that conjugation by $\bar w_1 j$ preserves, as an equivalence, both the local box of that order and the local box of $\Lambda_2$ at every $u\neq v_1$.
--
--   Galois action on the uniformisation. A homomorphism $\mathrm{dIso}_1$ from the decomposition subgroup to the isometric automorphisms of $K$ fixing $K_0$ is given, realising, by `hdIso₁`, the Galois action on $K$. A character $\chi_1$ from the decomposition subgroup to $\mathbb Z/2$ and, for each $j$, a ring map $\iota M_1 j:\mathbb T.\mathrm{objField}\,j\to\mathrm{Frac}(\mathrm{HolRingOf}\,\varpi_1\,\rho_1)$ are given, and `hI` asserts `DescentIntertwining` for the parameters $r=q'$, $ir=1$, $\overline{ir}=0$ at all of $A_1,\rho_1,\varpi_1,\Gamma_1,w_1,\bar w_1,s_1,\mathrm{dIso}_1,F_N,\mathbb T,\mathrm{galN},\mathrm{galT},W,WT,\chi_1,\iota M_1$: its first clauses require $\chi_1$ to be trivial on the inertia subgroup, to be nontrivial at every Frobenius element for $q'$, and to satisfy $\chi_1\tau=1$ if and only if $\tau$ fixes every element of the residue field of $A_1$ killed by $x\mapsto x^{q'^2}-x$, and require each $\iota M_1 j$ to carry constants from $\overline{\mathbb Q}$ to constants in $K$; the remaining clauses of the predicate tie the maps $\iota M_1 j$ to the Galois actions `galN`, `galT`, to the involutions $W$, $WT$ and to the elements $w_1,\bar w_1,s_1$, and are the compatibility conditions identifying the Galois action on the tower of curves with the action on the Mumford uniformisation.
--
--   The symmetry group. A group $S_1$ is given with a homomorphism $\mathrm{scalar}_1:S_1\to\mathrm{Dec}(A_1/\mathbb Q)$, a homomorphic section $\iota S_1$ of it (`hιS₁`), two elements $\sigma_{01},\sigma_{11}$, a character $\chi S_1:S_1\to\mathbb Z/2$, a sign character $\mathrm{sgn}_1:S_1\to\mathbb Z^\times$, and for each $j$ a homomorphism $\mathrm{galFC}_1 j$ from $S_1$ to the semilinear automorphisms over $K$ of the invariant field $\mathcal M_j=\mathrm{invariantFieldOf}\,K\,\mathbb H[\mathbb Q,a_2,b_2]^\times\,(\mathrm{HolRingOf}\,\varpi_1\,\rho_1)\,(\Gamma_1 j)$, the subfield of $\mathrm{Frac}(\mathrm{HolRingOf}\,\varpi_1\,\rho_1)$ fixed by $\Gamma_1 j$. The structural hypotheses are: `hgen₁`, every $\sigma\in S_1$ is of the form $\iota S_1(\tau)\,\sigma_{01}^u\,\sigma_{11}^v$; `hrel₁`, $\sigma_{01}^2=\sigma_{11}^2=1$, $\sigma_{01}$ and $\sigma_{11}$ commute, and both commute with the image of $\iota S_1$; `huniv₁`, the corresponding universal property, namely for every group $H$, homomorphism $f$ from the decomposition subgroup and commuting involutions $h_0,h_1$ of $H$ commuting with the image of $f$ there is a homomorphism $F:S_1\to H$ with $F\circ\iota S_1=f$, $F\sigma_{01}=h_0$, $F\sigma_{11}=h_1$; `hχS₁`, $\chi S_1\circ\iota S_1=\chi_1$, $\chi S_1(\sigma_{01})\neq1$ and $\chi S_1(\sigma_{11})=1$; `hsgnS₁`, $\mathrm{sgn}_1(\iota S_1\tau)=1$ when $\chi S_1(\iota S_1\tau)=1$ and $\mathrm{sgn}_1(\iota S_1\tau)=\mathrm{sgn}_1(\sigma_{01})$ otherwise, with $\mathrm{sgn}_1(\sigma_{01})=-1$ and $\mathrm{sgn}_1(\sigma_{11})=1$. The action is pinned by: `hbase₁`, the base automorphism of $\mathrm{galFC}_1 j(\sigma)$ on $K$ is $\mathrm{dIso}_1(\mathrm{scalar}_1\sigma)$; `hactD₁`, for $\tau$ in the decomposition subgroup, $\mathrm{galFC}_1 j(\iota S_1\tau)$ acts on $y\in\mathcal M_j$ by applying the ambient semilinear automorphism induced by $\mathrm{dIso}_1\tau$ to $y$ and then acting by $1$ if $\chi_1\tau=1$ and by $w_1 j$ otherwise; `hact₀₁`, $\mathrm{galFC}_1 j(\sigma_{01})$ acts as multiplication by the image of $w_1 j$; `hact₁₁`, $\mathrm{galFC}_1 j(\sigma_{11})$ acts as the image of $\bar w_1 j$.
--
--   Conclusion. There exist families of homomorphisms, indexed by $j\in\mathrm{Obj}(q,q')$,
--   $$\pi_V j:S_1\to\mathrm{Sym}\bigl(\rho_1(\Gamma_1 j)\backslash\mathrm{Vert}(R_0,K_0)\bigr),\qquad \pi_E j:S_1\to\mathrm{Sym}\bigl(\{e\in\rho_1(\Gamma_1 j)\backslash\mathrm{Dart}(\mathcal T)\ :\ \mathrm{vertexType}(\mathcal T,\mathrm{stdVertex})\,(e.\mathrm{out}.\mathrm{fst})=0\}\bigr),$$
--   where $\mathcal T$ is the Bruhat–Tits tree of $R_0$ over $K_0$, the quotients are the orbit quotients for the image subgroup $\rho_1(\Gamma_1 j)\le\mathrm{PGL}_2(K_0)$, and the dart-orbits are restricted to those whose chosen representative has tail of type $0$ (type being the graph distance to the standard vertex modulo $2$), such that all of the following hold.
--
--   First, for every $j$ and every vertex $v$, $\pi_V j(\sigma_{01})$ sends the orbit of $v$ to the orbit of $\rho_1(w_1 j)\cdot v$. Second, for every $j$ and $v$, $\pi_V j(\sigma_{11})$ sends the orbit of $v$ to the orbit of $\rho_1(\bar w_1 j)\cdot v$. Third, for every $j$ and every admissible dart-orbit $e$, the dart-orbit underlying $\pi_E j(\sigma_{01})e$ is the orbit of the reversal of $\rho_1(w_1 j)\cdot e.\mathrm{out}$. Fourth, the dart-orbit underlying $\pi_E j(\sigma_{11})e$ is the orbit of $\rho_1(\bar w_1 j)\cdot e.\mathrm{out}$, without reversal. Fifth, for every $j$ and every $\tau$ in the decomposition subgroup with $\chi_1\tau=1$, both $\pi_V j(\iota S_1\tau)$ and $\pi_E j(\iota S_1\tau)$ are the identity. Sixth, for every $j$ and every $\tau$ with $\chi_1\tau\neq1$, $\pi_V j(\iota S_1\tau)=\pi_V j(\sigma_{01})$ and $\pi_E j(\iota S_1\tau)=\pi_E j(\sigma_{01})$.
--
--   Seventh, the realisation-independence clause: for every $j$, every $\sigma\in S_1$, every unit $n$ of $\mathbb H[\mathbb Q,a_2,b_2]$ normalising $\Gamma_1 j$ and every isometric automorphism $t$ of $K$ over $K_0$, if $\mathrm{galFC}_1 j(\sigma)$ acts on every $y\in\mathcal M_j$ by first applying the ambient semilinear automorphism induced by $t$ and then acting by $n$, then: for every vertex $v$, $\pi_V j(\sigma)$ sends the orbit of $v$ to the orbit of $\rho_1(n)\cdot v$; and for every admissible dart-orbit $e$, if $\rho_1(n)$ lies in the type-preserving subgroup of $\mathrm{PGL}_2(K_0)$ for $\mathcal T$ and the standard vertex, then $\mathrm{sgn}_1\sigma=1$ and $\pi_E j(\sigma)e$ is the orbit of $\rho_1(n)\cdot e.\mathrm{out}$, while if $\rho_1(n)$ is not type-preserving, then $\mathrm{sgn}_1\sigma=-1$ and $\pi_E j(\sigma)e$ is the orbit of the reversal of $\rho_1(n)\cdot e.\mathrm{out}$.
--
--   On the Mumford side of the Čerednik–Drinfeld uniformisation at the place over $q'$, this provides the action of the Galois-plus-Atkin–Lehner symmetry group $S_1$ on the dual graph of the degenerate fibre, realised as the quotient of the Bruhat–Tits tree by the image of the level group, together with the statement that this action depends only on the group element and not on the pair (normalising quaternion unit, isometric coefficient automorphism) used to realise it on the Mumford function field. It is used in the construction of the quotient presentation of the class-set Hecke module, [`CerednikDrinfeld.exists_quotientPresentation_classSet_hecke_of_descentIntertwining_one_zero`](thm.html#CerednikDrinfeld.exists_quotientPresentation_classSet_hecke_of_descentIntertwining_one_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_perm_quotVert_quotEdge_realisation_independent_of_descentIntertwining_one_zero.lean

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

theorem CerednikDrinfeld.exists_perm_quotVert_quotEdge_realisation_independent_of_descentIntertwining_one_zero

    {a₂ b₂ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₂ : IsDefiniteRamifiedExactlyAt a₂ b₂ q)
    (Λ₂ R₂ : Submodule ℤ ℍ[ℚ, a₂, b₂]) (hΛ₂ : IsMaximalOrder Λ₂) (hR₂ : IsEichlerOrder R₂ N) (hRΛ₂ : R₂ ≤ Λ₂)
    (n₂ : (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₂ : n₂ ∈ primeHeckeSet R₂ q')
    (hS₂ : IsEichlerOrder (meetOrder R₂ n₂) (N * q'))
    (hnorm₂ : Submodule.conjByFiniteIdele (meetOrder R₂ n₂) n₂ = meetOrder R₂ n₂)
    (hsq₂ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)),
      classSetShift _ n₂ (classSetShift _ n₂ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    (hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂)

    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')

    (FN : Type) [Field FN] [Algebra (AlgebraicClosure ℚ) FN] [IsCurveOver (AlgebraicClosure ℚ) FN]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) FN]
    (𝕋 : HeckeTower.TowerData q q' FN)
    (hfg : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))
    (galN : ↥(A₁.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) FN)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A₁.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (hgalN : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galN τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (hgalT : ∀ ℓ (τ : ↥(A₁.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galT ℓ τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) FN) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

    [hiso₁ : Fact (A₁.DecompositionIsometric ℚ)]
    (v₁ : HeightOneSpectrum (𝓞 ℚ)) (hv₁ : ((q' : ℕ) : 𝓞 ℚ) ∈ v₁.asIdeal)

    (ι₁ : ℍ[ℚ, a₂, b₂] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (hι₁ : Function.Injective ι₁)
    (ρ₁ : (ℍ[ℚ, a₂, b₂])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₁)))
    (hρ₁ : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, ρ₁ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) x))

    (ϖ₁ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hϖ₁ : algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion ϖ₁.ϖ = ((q' : AlgebraicClosure ℚ) : A₁.valuation.Completion))
    [hdom₁ : IsDomain (Omega.HolRingOf ϖ₁ ρ₁)]

    (s₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (sf₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₁ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₁ ℓ : ℍ[ℚ, a₂, b₂]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₂, b₂]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₁ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₂ (meetOrder R₂ n₂) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₂ n₂) (ℓ.1 : ℕ)) ∧
      nrd (s₁ ℓ : ℍ[ℚ, a₂, b₂]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₁ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₂, b₂])ˣ)
    (hΓ₁0 : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, x ∈ Γ₁ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ Even (padicValRat q' (nrd (x : ℍ[ℚ, a₂, b₂]))))
    (hΓ₁ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₁ (some ℓ) = Γ₁ none ⊓ (Γ₁ none).map (MulAut.conj (s₁ ℓ)).toMonoidHom)

    (w₁ wbar₁ : HeckeTower.Obj q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (hw₁ : (w₁ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ nrd (w₁ none : ℍ[ℚ, a₂, b₂]) = (q' : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₁ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁ ∧ nrd (w₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q' : ℚ))
    (hwbar₁ :
      (nrd (wbar₁ none : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₁ none) ∈ Submodule.localBoxUnits R₂ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox R₂ u ↔
            x ∈ Submodule.localBox R₂ u) ∧
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
            x ∈ Submodule.localBox Λ₂ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₁ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₂ (sf₁ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
              x ∈ Submodule.localBox Λ₂ u))))

    (dIso₁ : ↥(A₁.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hdIso₁ : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : A₁.valuation.Completion), (dIso₁ τ).toRingEquiv x = τ • x)

    (χ₁ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (ιM₁ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁))
    (hI : CerednikDrinfeld.DescentIntertwining q' (1 : Fin 2) (0 : Fin 2) A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁
      FN 𝕋 galN galT W WT χ₁ ιM₁)

    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Algebra R₀ ↥(ValuationSubring.ratClosure A₁)] [IsFractionRing R₀ ↥(ValuationSubring.ratClosure A₁)] [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : ↥(ValuationSubring.ratClosure A₁), x ∈ Set.range (algebraMap R₀ ↥(ValuationSubring.ratClosure A₁)) ↔ Valued.v (algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion x) ≤ 1)

    (S₁ : Type) [Group S₁] (scalar₁ : S₁ →* ↥(A₁.decompositionSubgroup ℚ))
    (ιS₁ : ↥(A₁.decompositionSubgroup ℚ) →* S₁) (hιS₁ : ∀ τ, scalar₁ (ιS₁ τ) = τ)
    (σ₀₁ σ₁₁ : S₁) (χS₁ : S₁ →* Multiplicative (ZMod 2)) (sgn₁ : S₁ →* ℤˣ)
    (galFC₁ : ∀ j : HeckeTower.Obj q q', S₁ →* SemilinearAut A₁.valuation.Completion ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)))

    (hgen₁ : ∀ σ : S₁, ∃ (τ : ↥(A₁.decompositionSubgroup ℚ)) (u v : ℕ), σ = ιS₁ τ * σ₀₁ ^ u * σ₁₁ ^ v)
    (hrel₁ : σ₀₁ * σ₀₁ = 1 ∧ σ₁₁ * σ₁₁ = 1 ∧ σ₀₁ * σ₁₁ = σ₁₁ * σ₀₁ ∧
      (∀ τ, ιS₁ τ * σ₀₁ = σ₀₁ * ιS₁ τ) ∧ (∀ τ, ιS₁ τ * σ₁₁ = σ₁₁ * ιS₁ τ))
    (huniv₁ : ∀ (H : Type) [Group H] (f : ↥(A₁.decompositionSubgroup ℚ) →* H) (h₀ h₁ : H),
      h₀ * h₀ = 1 → h₁ * h₁ = 1 → h₀ * h₁ = h₁ * h₀ → (∀ τ, f τ * h₀ = h₀ * f τ) → (∀ τ, f τ * h₁ = h₁ * f τ) →
      ∃ F : S₁ →* H, (∀ τ, F (ιS₁ τ) = f τ) ∧ F σ₀₁ = h₀ ∧ F σ₁₁ = h₁)

    (hχS₁ : (∀ τ, χS₁ (ιS₁ τ) = χ₁ τ) ∧ χS₁ σ₀₁ ≠ 1 ∧ χS₁ σ₁₁ = 1)
    (hsgnS₁ : (∀ τ, χS₁ (ιS₁ τ) = 1 → sgn₁ (ιS₁ τ) = 1) ∧ (∀ τ, χS₁ (ιS₁ τ) ≠ 1 → sgn₁ (ιS₁ τ) = sgn₁ σ₀₁) ∧
      sgn₁ σ₀₁ = -1 ∧ sgn₁ σ₁₁ = 1)

    (hbase₁ : ∀ j (σ : S₁) (c : A₁.valuation.Completion), SemilinearAut.baseAut (galFC₁ j σ) c = (dIso₁ (scalar₁ σ)).toRingEquiv c)
    (hactD₁ : ∀ j (τ : ↥(A₁.decompositionSubgroup ℚ)) (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
      ((galFC₁ j (ιS₁ τ) • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
        (if χ₁ τ = 1 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else w₁ j) • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ τ)) (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)))
    (hact₀₁ : ∀ j (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))), ((galFC₁ j σ₀₁ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = (w₁ j) • (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)))
    (hact₁₁ : ∀ j (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))), ((galFC₁ j σ₁₁ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = (wbar₁ j) • (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) :
    ∃ (πV : ∀ j : HeckeTower.Obj q q', S₁ →* Equiv.Perm (Mumford.QuotVert ↥((Γ₁ j).map ρ₁) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₁))))
      (πE : ∀ j : HeckeTower.Obj q q', S₁ →* Equiv.Perm {e : Mumford.QuotEdge ↥((Γ₁ j).map ρ₁) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₁)) e.out.fst = 0}),

      (∀ j (v : LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₁)), πV j σ₀₁ (Quotient.mk (MulAction.orbitRel ↥((Γ₁ j).map ρ₁) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₁))) v) =
        Quotient.mk (MulAction.orbitRel ↥((Γ₁ j).map ρ₁) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₁))) (ρ₁ (w₁ j) • v)) ∧
      (∀ j (v : LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₁)), πV j σ₁₁ (Quotient.mk (MulAction.orbitRel ↥((Γ₁ j).map ρ₁) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₁))) v) =
        Quotient.mk (MulAction.orbitRel ↥((Γ₁ j).map ρ₁) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₁))) (ρ₁ (wbar₁ j) • v)) ∧
      (∀ j (e : {e : Mumford.QuotEdge ↥((Γ₁ j).map ρ₁) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₁)) e.out.fst = 0}), ((πE j σ₀₁ e).1 : Mumford.QuotEdge ↥((Γ₁ j).map ρ₁) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁))) =
        Quotient.mk (MulAction.orbitRel ↥((Γ₁ j).map ρ₁) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)).Dart) (ρ₁ (w₁ j) • e.1.out).symm) ∧
      (∀ j (e : {e : Mumford.QuotEdge ↥((Γ₁ j).map ρ₁) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₁)) e.out.fst = 0}), ((πE j σ₁₁ e).1 : Mumford.QuotEdge ↥((Γ₁ j).map ρ₁) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁))) =
        Quotient.mk (MulAction.orbitRel ↥((Γ₁ j).map ρ₁) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)).Dart) (ρ₁ (wbar₁ j) • e.1.out)) ∧
      (∀ j (τ : ↥(A₁.decompositionSubgroup ℚ)), χ₁ τ = 1 → πV j (ιS₁ τ) = 1 ∧ πE j (ιS₁ τ) = 1) ∧
      (∀ j (τ : ↥(A₁.decompositionSubgroup ℚ)), χ₁ τ ≠ 1 → πV j (ιS₁ τ) = πV j σ₀₁ ∧ πE j (ιS₁ τ) = πE j σ₀₁) ∧

      (∀ j (σ : S₁) (n : (ℍ[ℚ, a₂, b₂])ˣ) (t : Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion),
        n ∈ Subgroup.normalizer ((Γ₁ j : Subgroup (ℍ[ℚ, a₂, b₂])ˣ) : Set (ℍ[ℚ, a₂, b₂])ˣ) →
        (∀ y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)), ((galFC₁ j σ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ t) (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) →
        (∀ v : (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₁)), πV j σ ((Quotient.mk (MulAction.orbitRel ↥((Γ₁ j).map ρ₁) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₁))) v)) = (Quotient.mk (MulAction.orbitRel ↥((Γ₁ j).map ρ₁) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₁))) (ρ₁ n • v))) ∧
        (∀ e : {e : Mumford.QuotEdge ↥((Γ₁ j).map ρ₁) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₁)) e.out.fst = 0},
          (ρ₁ n ∈ Mumford.typePreserving PGL(2, ↥(ValuationSubring.ratClosure A₁)) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₁)) → sgn₁ σ = 1 ∧ (πE j σ e).1 = Quotient.mk (MulAction.orbitRel ↥((Γ₁ j).map ρ₁) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)).Dart) (ρ₁ n • e.1.out)) ∧
          (ρ₁ n ∉ Mumford.typePreserving PGL(2, ↥(ValuationSubring.ratClosure A₁)) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₁)) → sgn₁ σ = -1 ∧ (πE j σ e).1 = Quotient.mk (MulAction.orbitRel ↥((Γ₁ j).map ρ₁) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₁)).Dart) (ρ₁ n • e.1.out).symm))) := by sorry
