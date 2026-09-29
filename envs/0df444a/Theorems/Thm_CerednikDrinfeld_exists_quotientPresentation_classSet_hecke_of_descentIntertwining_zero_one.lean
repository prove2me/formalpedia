-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_quotientPresentation_classSet_hecke_of_descentIntertwining_zero_one
-- name    : CerednikDrinfeld.exists_quotientPresentation_classSet_hecke_of_descentIntertwining_zero_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/378d783f-fe6c-59e2-b857-e4bae2535132
-- title:
--   Quotient-graph presentation at q with class set and Hecke
-- statement:
--   **The arithmetic data.** Fix rationals $a_1,b_1$ and write $\mathbb H=\mathbb H[\mathbb Q,a_1,b_1]$ for the associated quaternion algebra; fix a nonzero squarefree $N$ and primes $q,q'$ with $q'\neq q$, $5\le q$, $5\le q'$, and $q\nmid N$, $q'\nmid N$. The hypothesis `hdef₁` is `IsDefiniteRamifiedExactlyAt a₁ b₁ q'`: $a_1<0$, $b_1<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb Q$ every nonzero element of $\mathbb H\otimes_{\mathbb Q}\mathbb Q_v$ is a unit if and only if $q'$ lies in $v$. Further, $\Lambda_1$ is a maximal order (an order — a finitely generated $\mathbb Z$-submodule containing $1$, closed under multiplication and spanning $\mathbb H$ over $\mathbb Q$ — maximal among orders containing it), $R_1$ is an Eichler order of level $N$ (an intersection of two maximal orders, of relative index $N$ in the first), and $R_1\le\Lambda_1$. The finite idele $n_1\in(\mathbb H\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{\mathrm f})^\times$ lies in `primeHeckeSet R₁ q`, i.e. $n_1$ and $q\,n_1^{-1}$ lie in the finite adelic box of $R_1$ while $n_1^{-1}$ and $q^{-1}n_1$ do not. The order $R_1\cap n_1R_1n_1^{-1}$ (written `meetOrder R₁ n₁`) is Eichler of level $Nq$ (`hS₁`) and is preserved by conjugation by $n_1$ (`hnorm₁`); the shift by $n_1$ on the class set of the finite-idele stabiliser of `meetOrder R₁ n₁` is an involution (`hsq₁`); the two class sets occurring are finite. The hypothesis `hlaws₁` is `ClassSetHeckeLaws N q Λ₁ R₁ n₁`, whose four clauses require the edge Hecke matrices `classSetEdgeHecke N q Λ₁ R₁ n₁` to commute pairwise, the vertex Hecke matrices `classSetVertexHecke N Λ₁ R₁` to commute pairwise, the two degeneracy pushforwards of `classSetDegeneracyData R₁ n₁` to intertwine the edge and vertex operators at every prime $\ell\neq q$, and the joint kernel of those pushforwards to be stable under all edge operators.
--
--   **The place above $q$ and the tower.** $A_2$ is a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A_2$ (`hA₂`), whose decomposition group over $\mathbb Q$ acts isometrically for the valuation (`hiso₂`), and $v_2$ is a height-one prime of the ring of integers of $\mathbb Q$ containing $q$ (`hv₂`). The field $F_N$ is a curve over $\overline{\mathbb Q}$ in the sense of `IsCurveOver` (principal divisors of degree zero exist, all residue fields of places are finite over $\overline{\mathbb Q}$, and the module of Kähler differentials is free of rank one) and is essentially of finite type over $\overline{\mathbb Q}$; $\mathbb T$ is a `HeckeTower.TowerData q q' FN`, assigning to each prime $\ell\notin\{q,q'\}$ a curve field $\mathbb T.F\,\ell$ over $\overline{\mathbb Q}$ together with, for each of the two arrows $(\ell,0),(\ell,1)$, a $\overline{\mathbb Q}$-algebra map $F_N\to\mathbb T.F\,\ell$ that is finite along and integral; the levels of the tower are indexed by `HeckeTower.Obj q q'`$=$`Option (AwayPrime q q')`, the base level being `none`. By `hfg` each field of the tower is finite-dimensional over $\overline{\mathbb Q}(x)$ for some transcendental $x$. The maps $\mathrm{gal}_N$ and $\mathrm{gal}_T\ \ell$ send the decomposition group of $A_2$ over $\mathbb Q$ to semilinear automorphisms of $F_N$, respectively of $\mathbb T.F\,\ell$, whose base automorphism of $\overline{\mathbb Q}$ is the given element (`hgalN`, `hgalT`); $W$ and $W_T\ \ell$ are two further semilinear automorphisms at each level.
--
--   **The local Čerednik–Drinfeld data.** $\iota_2:\mathbb H\to M_2(\,$`ratClosure A₂`$)$ is an injective $\mathbb Q$-algebra map into the matrix algebra over the closure of $\mathbb Q$ inside the completion of $\overline{\mathbb Q}$ at $A_2$, and $\rho_2:\mathbb H^\times\to \mathrm{PGL}_2$ of that field is its projectivisation (`hρ₂`). The pseudo-uniformiser $\varpi_2$ has image $q$ in the completion (`hϖ₂`), and the holomorphic ring `HolRingOf ϖ₂ ρ₂` is a domain. The families $s_2,\ sf_2$ satisfy `hs₂`: for each $\ell$, the $u$-component of $sf_2\,\ell$ is $s_2\,\ell\otimes 1$ at every finite place $u$ not containing $q$ and is $1$ at the places containing $q$; the product of the diagonal idele of the scalar $\ell$ with $(sf_2\,\ell)^{-1}$ lies in `levelHeckeUSet Λ₁ (meetOrder R₁ n₁) ℓ` if $\ell\mid N$ and in `primeHeckeSet (meetOrder R₁ n₁) ℓ` otherwise; and $\mathrm{nrd}(s_2\,\ell)=\ell$. The level groups $\Gamma_2$ satisfy `hΓ₂0`: $\Gamma_2(\mathrm{none})$ consists of the units of $\mathbb H$ lying in `awayUnits R₁ v₂` (local units of $R_1$ at every place other than $v_2$) whose reduced norm has even $q$-adic valuation; and `hΓ₂ℓ`: $\Gamma_2(\mathrm{some}\ \ell)=\Gamma_2(\mathrm{none})\cap s_2\ell\,\Gamma_2(\mathrm{none})\,(s_2\ell)^{-1}$. By `hw₂`, $w_2(\mathrm{none})\in$`awayUnits R₁ v₂` with $\mathrm{nrd}=q$, and $w_2(\mathrm{some}\ \ell)\in$`awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂` with $\mathrm{nrd}=q$. By `hwbar₂`, at the base level $\mathrm{nrd}(\bar w_2(\mathrm{none}))=q'$, the image of $\bar w_2(\mathrm{none})$ at each place $u\neq v_2$ not containing $q'$ is a local unit of $R_1$, and conjugation by $\bar w_2(\mathrm{none})$ preserves, in both directions, the local boxes of $R_1$ and of $\Lambda_1$ at every $u\neq v_2$; the same three conditions hold at each level $\ell$ with $R_1$ replaced by `meetOrder R₁ (sf₂ ℓ)` and $\Lambda_1$ unchanged. The map $\mathrm{dIso}_2$ sends the decomposition group to isometric automorphisms of the completion realising the Galois action (`hdIso₂`), $\chi_2$ is a character of the decomposition group with values in $\mathbb Z/2$ written multiplicatively, and $\iota^M_2 j$ embeds the $j$-th field of the tower into the fraction field of `HolRingOf ϖ₂ ρ₂`. The hypothesis `hI` is `DescentIntertwining q 0 1 A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂ FN 𝕋 galN galT W WT χ₂ ιM₂`, with the prime $q$ in the numerical slot and $0,1$ as the two distinguished indices; among its clauses, $\chi_2$ is trivial on the inertia subgroup of $A_2$, nontrivial on every Frobenius at $q$, and trivial exactly on those $\tau$ fixing all $x$ in the residue field of $A_2$ with $x^{q^2}=x$, and each $\iota^M_2 j$ is compatible with the structure maps from $\overline{\mathbb Q}$ into the completion; its remaining clauses tie the tower $\mathbb T$, its semilinear Galois actions and its distinguished automorphisms $W,W_T$ to the Mumford fields through $\iota^M_2$.
--
--   **The coefficient ring and the symmetry group.** $R_0$ is a discrete valuation ring with finite residue field whose fraction field is `ratClosure A₂`, its image consisting exactly of the elements of valuation at most $1$ in the completion (`hR₀`). The group $S_2$ comes with a homomorphism $\mathrm{scalar}_2$ to the decomposition group and a section $\iota_{S_2}$ of it (`hιS₂`), two elements $\sigma_{0},\sigma_{1}$, characters $\chi_{S_2}$ with values in $\mathbb Z/2$ and $\mathrm{sgn}_2$ with values in $\mathbb Z^\times$, and for each level $j$ an action $\mathrm{galFC}_2 j$ of $S_2$ by semilinear automorphisms of the subfield of the fraction field of `HolRingOf ϖ₂ ρ₂` fixed pointwise by $\Gamma_2 j$. The hypotheses on $S_2$ are: `hgen₂`, every $\sigma$ has the form $\iota_{S_2}(\tau)\sigma_0^{u}\sigma_1^{v}$; `hrel₂`, the five relations $\sigma_0^2=\sigma_1^2=1$, $\sigma_0\sigma_1=\sigma_1\sigma_0$, and $\sigma_0,\sigma_1$ each commute with the image of $\iota_{S_2}$; `huniv₂`, the corresponding universal property (any homomorphism from the decomposition group to a group $H$, together with two commuting involutions of $H$ commuting with its image, extends to a homomorphism from $S_2$ sending $\iota_{S_2}(\tau)\mapsto f(\tau)$, $\sigma_0\mapsto h_0$, $\sigma_1\mapsto h_1$); `hχS₂`, $\chi_{S_2}\circ\iota_{S_2}=\chi_2$, $\chi_{S_2}(\sigma_0)\neq 1$, $\chi_{S_2}(\sigma_1)=1$; `hsgnS₂`, $\mathrm{sgn}_2(\iota_{S_2}\tau)=1$ when $\chi_{S_2}(\iota_{S_2}\tau)=1$ and $=\mathrm{sgn}_2(\sigma_0)$ otherwise, with $\mathrm{sgn}_2(\sigma_0)=-1$ and $\mathrm{sgn}_2(\sigma_1)=1$; `hbase₂`, the base automorphism of $\mathrm{galFC}_2 j\sigma$ on the completion is $\mathrm{dIso}_2(\mathrm{scalar}_2\sigma)$; and the three action formulas `hactD₂`, `hact₀₂`, `hact₁₂`: for $y$ in the $\Gamma_2 j$-invariant field, $\mathrm{galFC}_2 j(\iota_{S_2}\tau)\cdot y$ equals $(1$ if $\chi_2\tau=1$, else $w_2 j)$ acting on the image of $y$ under the coefficient automorphism induced by $\mathrm{dIso}_2\tau$, while $\mathrm{galFC}_2 j(\sigma_0)\cdot y=w_2 j\cdot y$ and $\mathrm{galFC}_2 j(\sigma_1)\cdot y=\bar w_2 j\cdot y$.
--
--   **Conclusion.** Under these hypotheses there exist families of finite types with decidable equality $E j, V j$ indexed by the levels $j$, for each $j$ a degeneracy datum $D j$ on $(E j, V j)$ (two maps $a,b:E j\to V j$ and a width $w:E j\to\mathbb N_{>0}$), bijections
--   $$e^V_j:\ \rho_2(\Gamma_2 j)\backslash\{\text{vertices of the Bruhat–Tits tree of }R_0\}\ \xrightarrow{\ \sim\ }\ V j,$$
--   $$e^E_j:\ \{\text{orbits }e\text{ of darts with }\mathrm{vertexType}(e.\mathrm{out}.\mathrm{fst})=0\}\ \xrightarrow{\ \sim\ }\ E j,$$
--   where the tree is `BruhatTits.tree R₀ (ratClosure A₂)` on homothety classes of full lattices and the type of a vertex is its distance modulo $2$ from the standard vertex, homomorphisms $\pi^V_2 j,\pi^E_2 j$ from $S_2$ to the permutation groups of $V j$ and of $E j$, a homomorphism $\mathrm{actZ}_2 j$ from $S_2$ to the $\mathbb Z$-linear automorphisms of the ribbon kernel of $D j$ (the functions $x:E j\to\mathbb Z$ whose pushforwards along $a$ and along $b$ vanish), a bijection $c^E_2$ from the class set of the finite-idele stabiliser of `meetOrder R₁ n₁` to $E(\mathrm{none})$, a $\mathbb Z$-linear isomorphism $e_2$ from the ribbon kernel of $D(\mathrm{none})$ to that of `classSetDegeneracyData R₁ n₁` (whose $a$ is the forgetful map of class sets, whose $b$ is the shift by $n_1$, and whose width is `classWeight`, the `unitWeight` of `meetOrder R₁ n₁` conjugated by a representative idele), and for each arrow $\alpha$ of the tower a finite homomorphism $\mu^F_2\alpha$ of degeneracy data from $D(\mathrm{some}\ \alpha_1)$ to $D(\mathrm{none})$, such that all of the following hold.
--
--   (i) For every $j$, $\rho_2(\Gamma_2 j)$ is contained in the type-preserving subgroup of $\mathrm{PGL}_2$ for the tree and the standard vertex. (ii) For every $j$ and every dart $d$, the stabiliser of $d$ in $\rho_2(\Gamma_2 j)$ is finite. (iii)–(v) For every $j$ and every type-$0$ dart orbit $e$: $(D j).a(e^E_j e)$ is $e^V_j$ of the vertex orbit of the origin of $e.\mathrm{out}$; $(D j).b(e^E_j e)$ is $e^V_j$ of the vertex orbit of its terminus; and $(D j).w(e^E_j e)$ is the cardinality of the stabiliser of $e.\mathrm{out}$ in $\rho_2(\Gamma_2 j)$.
--
--   (vi) (Realisation of the symmetries.) For every $j$, every $\sigma\in S_2$, every $n\in\mathbb H^\times$ normalising $\Gamma_2 j$ and every isometric automorphism $t$ of the completion, if $\mathrm{galFC}_2 j\sigma$ acts on the $\Gamma_2 j$-invariant field by $y\mapsto n\cdot(\text{coefficient transport by }t)(y)$, then: for every vertex $v$, $\pi^V_2 j\sigma$ carries $e^V_j$ of the orbit of $v$ to $e^V_j$ of the orbit of $\rho_2(n)\cdot v$; and for every type-$0$ dart orbit $e$, if $\rho_2(n)$ is type-preserving then $\mathrm{sgn}_2\sigma=1$ and the dart orbit underlying $(e^E_j)^{-1}(\pi^E_2 j\sigma(e^E_j e))$ is the orbit of $\rho_2(n)\cdot e.\mathrm{out}$, whereas if $\rho_2(n)$ is not type-preserving then $\mathrm{sgn}_2\sigma=-1$ and that dart orbit is the orbit of the reversal of $\rho_2(n)\cdot e.\mathrm{out}$.
--
--   (vii) For every $j$ and every $\tau$ in the decomposition group with $\chi_{S_2}(\iota_{S_2}\tau)=1$: $\pi^V_2 j(\iota_{S_2}\tau)=1$, $\pi^E_2 j(\iota_{S_2}\tau)=1$ and $\mathrm{sgn}_2(\iota_{S_2}\tau)=1$. (viii) For every $j$ and every $\tau$ with $\chi_{S_2}(\iota_{S_2}\tau)\neq 1$: $\pi^V_2 j(\iota_{S_2}\tau)=\pi^V_2 j(\sigma_0)$, $\pi^E_2 j(\iota_{S_2}\tau)=\pi^E_2 j(\sigma_0)$ and $\mathrm{sgn}_2(\iota_{S_2}\tau)=\mathrm{sgn}_2(\sigma_0)$.
--
--   (ix) The permutations $\pi^E_2 j\sigma$ preserve the widths of $D j$. (x) If $\mathrm{sgn}_2\sigma=1$ then $a$ and $b$ are equivariant, $(D j).a(\pi^E_2 j\sigma\,e')=\pi^V_2 j\sigma((D j).a\,e')$ and likewise for $b$; if $\mathrm{sgn}_2\sigma=-1$ then $a$ and $b$ are interchanged, $(D j).a(\pi^E_2 j\sigma\,e')=\pi^V_2 j\sigma((D j).b\,e')$ and $(D j).b(\pi^E_2 j\sigma\,e')=\pi^V_2 j\sigma((D j).a\,e')$. (xi) For all $\sigma$, all $x$ in the ribbon kernel of $D j$ and all $e'\in E j$, $(\mathrm{actZ}_2 j\sigma\,x)(\pi^E_2 j\sigma\,e')=\mathrm{sgn}_2(\sigma)\cdot x(e')$.
--
--   (xii) At the base level, $\pi^E_2(\mathrm{none})(\sigma_0)$ transports $c^E_2$ to the shift by $n_1$: $\pi^E_2(\mathrm{none})(\sigma_0)(c^E_2 c)=c^E_2(\text{shift of }c\text{ by }n_1)$ for every class $c$. (xiii) The isomorphism $e_2$ is the coordinate change along $c^E_2$: $(e_2 x)(c)=x(c^E_2 c)$ for all $x$ in the ribbon kernel of $D(\mathrm{none})$ and all classes $c$. (xiv) $e_2$ is an isometry for the width pairings: the ribbon Gram form of `classSetDegeneracyData R₁ n₁` evaluated at $(e_2x,e_2y)$ equals that of $D(\mathrm{none})$ at $(x,y)$. (xv) Under $e_2$, the action of $\sigma_1$ becomes the Hecke operator at $q'$: $e_2(\mathrm{actZ}_2(\mathrm{none})(\sigma_1)(e_2^{-1}z))$ equals `heckeKernelMap (classSetHeckeData N q Λ₁ R₁ n₁) ⟨q', _⟩ z` for every $z$ in the ribbon kernel of `classSetDegeneracyData R₁ n₁`.
--
--   (xvi)–(xvii) For each arrow $\alpha=(\ell,i)$, writing $g_\alpha=\rho_2(1)$ if $i=0$ and $g_\alpha=\rho_2(s_2\ell)$ if $i=1$: the vertex map of $\mu^F_2\alpha$ sends $e^V_{\mathrm{some}\,\ell}$ of the orbit of $v$ to $e^V_{\mathrm{none}}$ of the orbit of $g_\alpha^{-1}\cdot v$, and the dart orbit underlying $(e^E_{\mathrm{none}})^{-1}$ of the edge map applied to $e^E_{\mathrm{some}\,\ell}e$ is the orbit of $g_\alpha^{-1}\cdot e.\mathrm{out}$. (xviii) The total degree of $\mu^F_2\alpha$ equals `HeckeTower.arrowDegree N α`, that is $\ell$ if $\ell\mid N$ and $\ell+1$ otherwise. (xix) The edge maps of the $\mu^F_2\alpha$ commute with the $S_2$-actions: $(\mu^F_2\alpha).\mathrm{mapE}(\pi^E_2(\mathrm{some}\ \alpha_1)\sigma\,e')=\pi^E_2(\mathrm{none})\sigma((\mu^F_2\alpha).\mathrm{mapE}\,e')$. (xx) Push–pull along the two arrows at $\ell$ realises the Hecke operator at $\ell$: for every $\ell$ and every $z$ in the ribbon kernel of `classSetDegeneracyData R₁ n₁`,
--   $$e_2\bigl((\mu^F_2(\ell,0)).\mathrm{pushforward}\bigl((\mu^F_2(\ell,1)).\mathrm{pullback}(e_2^{-1}z)\bigr)\bigr)=\mathtt{heckeKernelMap (classSetHeckeData N q Λ₁ R₁ n₁)}\ \ell\ z,$$
--   where pullback multiplies the $e$-coordinate by the local degree of $\mu^F_2(\ell,1)$ at $e$ and pushforward sums over the fibres of the edge map of $\mu^F_2(\ell,0)$.
--
--   This is the Mumford side of the Čerednik–Drinfeld uniformisation at the prime $q$ in graph-theoretic form: it presents, uniformly in the levels of the Hecke tower, the quotient of the Bruhat–Tits tree by the relevant arithmetic subgroups of a definite quaternion algebra ramified exactly at $q'$ as a finite degeneracy datum, identifies the base-level edge set with the class set of an Eichler order of level $Nq$, and matches the Atkin–Lehner involution $\sigma_1$ and the push–pull along the tower's arrows with the class-set Hecke operators. It supplies the graph, transport and Hecke data used in the construction of a Shimura-curve model with good reduction together with its equivariant uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_quotientPresentation_classSet_hecke_of_descentIntertwining_zero_one.lean

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
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open ModularCurve
open AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

set_option maxHeartbeats 400000 in

theorem CerednikDrinfeld.exists_quotientPresentation_classSet_hecke_of_descentIntertwining_zero_one

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
    ∃ (E V : HeckeTower.Obj q q' → Type) (_ : ∀ j, Fintype (E j)) (_ : ∀ j, Fintype (V j))
      (_ : ∀ j, DecidableEq (E j)) (_ : ∀ j, DecidableEq (V j))

      (D : ∀ j : HeckeTower.Obj q q', DegeneracyData (E j) (V j))
      (eV : ∀ j : HeckeTower.Obj q q', Mumford.QuotVert ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂)) ≃ V j)
      (eE : ∀ j : HeckeTower.Obj q q', {e : Mumford.QuotEdge ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) e.out.fst = 0} ≃ E j)

      (πV₂ : ∀ j, S₂ →* Equiv.Perm (V j)) (πE₂ : ∀ j, S₂ →* Equiv.Perm (E j))
      (actZ₂ : ∀ j, S₂ →* (↥(ribbonKernel (D j)) ≃ₗ[ℤ] ↥(ribbonKernel (D j))))

      (cE₂ : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)) ≃ E none)
      (e₂ : ↥(ribbonKernel (D none)) ≃ₗ[ℤ] ↥(ribbonKernel (classSetDegeneracyData R₁ n₁)))

      (μF₂ : ∀ α : HeckeTower.Arr q q', DegeneracyData.FiniteHom (D (HeckeTower.dom α)) (D (HeckeTower.cod α))),

      (∀ j, (Γ₂ j).map ρ₂ ≤ Mumford.typePreserving PGL(2, ↥(ValuationSubring.ratClosure A₂)) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂))) ∧
      (∀ j (d : (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)).Dart), Finite (MulAction.stabilizer ↥((Γ₂ j).map ρ₂) d)) ∧

      (∀ j (e : {e : Mumford.QuotEdge ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) e.out.fst = 0}), (D j).a (eE j e) = eV j (Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) e.1.out.fst)) ∧
      (∀ j (e : {e : Mumford.QuotEdge ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) e.out.fst = 0}), (D j).b (eE j e) = eV j (Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) e.1.out.snd)) ∧
      (∀ j (e : {e : Mumford.QuotEdge ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) e.out.fst = 0}), ((D j).w (eE j e) : ℕ) = Nat.card (MulAction.stabilizer ↥((Γ₂ j).map ρ₂) e.1.out)) ∧

      (∀ j (σ : S₂) (n : (ℍ[ℚ, a₁, b₁])ˣ) (t : Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion),
        n ∈ Subgroup.normalizer ((Γ₂ j : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) : Set (ℍ[ℚ, a₁, b₁])ˣ) →
        (∀ y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j)), ((galFC₂ j σ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ t) (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) →
        (∀ v : (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂)), πV₂ j σ (eV j (Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) v)) = eV j (Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) (ρ₂ n • v))) ∧
        (∀ e : {e : Mumford.QuotEdge ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) e.out.fst = 0},
          (ρ₂ n ∈ Mumford.typePreserving PGL(2, ↥(ValuationSubring.ratClosure A₂)) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) → sgn₂ σ = 1 ∧ ((eE j).symm (πE₂ j σ (eE j e))).1 = Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)).Dart) (ρ₂ n • e.1.out)) ∧
          (ρ₂ n ∉ Mumford.typePreserving PGL(2, ↥(ValuationSubring.ratClosure A₂)) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) → sgn₂ σ = -1 ∧ ((eE j).symm (πE₂ j σ (eE j e))).1 = Quotient.mk (MulAction.orbitRel ↥((Γ₂ j).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)).Dart) (ρ₂ n • e.1.out).symm))) ∧

      (∀ j (τ : ↥(A₂.decompositionSubgroup ℚ)), χS₂ (ιS₂ τ) = 1 →
        πV₂ j (ιS₂ τ) = 1 ∧ πE₂ j (ιS₂ τ) = 1 ∧ sgn₂ (ιS₂ τ) = 1) ∧
      (∀ j (τ : ↥(A₂.decompositionSubgroup ℚ)), χS₂ (ιS₂ τ) ≠ 1 →
        πV₂ j (ιS₂ τ) = πV₂ j σ₀₂ ∧ πE₂ j (ιS₂ τ) = πE₂ j σ₀₂ ∧ sgn₂ (ιS₂ τ) = sgn₂ σ₀₂) ∧

      (∀ j σ e', (D j).w (πE₂ j σ e') = (D j).w e') ∧
      (∀ j σ e', sgn₂ σ = 1 → (D j).a (πE₂ j σ e') = πV₂ j σ ((D j).a e') ∧ (D j).b (πE₂ j σ e') = πV₂ j σ ((D j).b e')) ∧
      (∀ j σ e', sgn₂ σ = -1 → (D j).a (πE₂ j σ e') = πV₂ j σ ((D j).b e') ∧ (D j).b (πE₂ j σ e') = πV₂ j σ ((D j).a e')) ∧
      (∀ j (σ : S₂) (x : ↥(ribbonKernel (D j))) (e' : E j),
        (actZ₂ j σ x : E j → ℤ) (πE₂ j σ e') = ((sgn₂ σ : ℤˣ) : ℤ) * (x : E j → ℤ) e') ∧

      (∀ c : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)), πE₂ none σ₀₂ (cE₂ c) = cE₂ (classSetShift _ n₁ c)) ∧
      (∀ (x : ↥(ribbonKernel (D none))) (c : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁))),
        ((e₂ x : ↥(ribbonKernel (classSetDegeneracyData R₁ n₁))) : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)) → ℤ) c = (x : E none → ℤ) (cE₂ c)) ∧
      (∀ x y : ↥(ribbonKernel (D none)), ribbonGram (classSetDegeneracyData R₁ n₁) (e₂ x) (e₂ y) = ribbonGram (D none) x y) ∧
      (∀ z : ↥(ribbonKernel (classSetDegeneracyData R₁ n₁)), e₂ (actZ₂ none σ₁₂ (e₂.symm z)) = heckeKernelMap (classSetHeckeData N q Λ₁ R₁ n₁) ⟨q', Fact.out⟩ z) ∧

      (∀ (α : HeckeTower.Arr q q') (v : (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))),
        (μF₂ α).mapV (eV (HeckeTower.dom α) (Quotient.mk (MulAction.orbitRel ↥((Γ₂ (HeckeTower.dom α)).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) v)) =
          eV (HeckeTower.cod α) (Quotient.mk (MulAction.orbitRel ↥((Γ₂ (HeckeTower.cod α)).map ρ₂) (LT.LatticeTree.Vertex R₀ ↥(ValuationSubring.ratClosure A₂))) ((ρ₂ (if α.2 = 0 then (1 : (ℍ[ℚ, a₁, b₁])ˣ) else s₂ α.1))⁻¹ • v))) ∧
      (∀ (α : HeckeTower.Arr q q') (e : {e : Mumford.QuotEdge ↥((Γ₂ (HeckeTower.dom α)).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) // Mumford.vertexType (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)) (LT.LatticeTree.stdVertex R₀ ↥(ValuationSubring.ratClosure A₂)) e.out.fst = 0}),
        ((eE (HeckeTower.cod α)).symm ((μF₂ α).mapE (eE (HeckeTower.dom α) e))).1 =
          Quotient.mk (MulAction.orbitRel ↥((Γ₂ (HeckeTower.cod α)).map ρ₂) (BruhatTits.tree R₀ ↥(ValuationSubring.ratClosure A₂)).Dart) ((ρ₂ (if α.2 = 0 then (1 : (ℍ[ℚ, a₁, b₁])ˣ) else s₂ α.1))⁻¹ • e.1.out)) ∧
      (∀ α : HeckeTower.Arr q q', ((μF₂ α).degTotal : ℕ) = HeckeTower.arrowDegree N α) ∧
      (∀ (α : HeckeTower.Arr q q') (σ : S₂) (e' : E (HeckeTower.dom α)),
        (μF₂ α).mapE (πE₂ (HeckeTower.dom α) σ e') = πE₂ (HeckeTower.cod α) σ ((μF₂ α).mapE e')) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (z : ↥(ribbonKernel (classSetDegeneracyData R₁ n₁))),
        e₂ ((μF₂ (ℓ, 0)).pushforward ((μF₂ (ℓ, 1)).pullback (e₂.symm z))) = heckeKernelMap (classSetHeckeData N q Λ₁ R₁ n₁) ℓ.1 z) := by sorry
