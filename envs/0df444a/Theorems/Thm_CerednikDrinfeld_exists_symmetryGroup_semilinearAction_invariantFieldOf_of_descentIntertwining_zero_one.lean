-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_zero_one
-- name    : CerednikDrinfeld.exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_zero_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/73a30d0a-3e28-5043-afbe-82325cc6029f
-- title:
--   Symmetry group of the Čerednik–Drinfeld tower at q
-- statement:
--   Throughout, $H=\mathbb H[\mathbb Q,a_1,b_1]$ is the quaternion algebra over $\mathbb Q$ with parameters $a_1,b_1$, $\mathbb A_f$ is the finite adele ring of $\mathbb Q$, $D=A_2.\mathrm{decompositionSubgroup}\ \mathbb Q$ is the decomposition subgroup of the valuation subring $A_2\subseteq\overline{\mathbb Q}$ inside $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$, $C=A_2.\mathrm{valuation}.\mathrm{Completion}$ is the completion of $\overline{\mathbb Q}$ at the valuation of $A_2$, $K_0=\mathtt{ValuationSubring.ratClosure}\ A_2$ is the topological closure of the prime subfield in $C$, $\mathcal O=\mathtt{Omega.HolRingOf}\ \varpi_2\ \rho_2$ is the ring of functions on Drinfeld's upper half-plane over $C$ that are holomorphic on each affinoid of the $\varpi_2$-exhaustion, and for an object $j$ of the Hecke tower $\mathcal M_j=\mathtt{Mumford.invariantFieldOf}\ C\ H^\times\ \mathcal O\ (\Gamma_2\,j)$ is the subfield of $\mathrm{Frac}(\mathcal O)$ of elements fixed by every element of $\Gamma_2\,j$ (the action of $H^\times$ being the one induced by $\rho_2$).
--
--   **Numerical data.** $N$ is a nonzero squarefree natural number, $q$ and $q'$ are primes with $q'\neq q$, $q\nmid N$, $q'\nmid N$, and $q,q'\geq 5$.
--
--   **Quaternionic data.** The hypothesis `hdef₁` says that $a_1<0$, $b_1<0$ and that for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $H\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra (every nonzero element is a unit) exactly when $q'\in v$; thus $H$ is definite and ramified at the finite place above $q'$ and nowhere else. Further, $\Lambda_1$ is a maximal order of $H$ (an order maximal among the orders containing it), $R_1$ is an Eichler order of level $N$ (an intersection of two maximal orders whose relative index in the first is $N$), and $R_1\leq\Lambda_1$.
--
--   **Hecke element and class-set data.** The unit $n_1\in(H\otimes_{\mathbb Q}\mathbb A_f)^\times$ lies in $\mathtt{primeHeckeSet}\ R_1\ q$, i.e. $n_1$ lies in the finite adele box of $R_1$, $q\cdot n_1^{-1}$ lies in that box, while $n_1^{-1}$ and $q^{-1}n_1$ do not. Writing $S_1=\mathtt{meetOrder}\ R_1\ n_1=R_1\cap n_1R_1n_1^{-1}$ (the conjugate being taken in the sense of [`Submodule.conjByFiniteIdele`](def/Submodule_FiniteAdeleBox.html#L31)), the hypotheses require: $S_1$ is an Eichler order of level $Nq$ (`hS₁`); $n_1$ normalises $S_1$ in the same sense, $\mathtt{conjByFiniteIdele}\ S_1\ n_1=S_1$ (`hnorm₁`); right translation by $n_1$ is an involution of the class set of the finite idele stabiliser of $S_1$, i.e. $\mathtt{classSetShift}$ applied twice is the identity (`hsq₁`); and `hlaws₁` is the predicate $\mathtt{ClassSetHeckeLaws}\ N\ q\ \Lambda_1\ R_1\ n_1$, a conjunction of four clauses: the edge Hecke matrices commute pairwise, the vertex Hecke matrices commute pairwise, for every prime $\ell\neq q$ and each of the two degeneracy pushforwards the edge Hecke operator at $\ell$ is carried to the vertex Hecke operator at $\ell$, and for every prime $\ell$ the common kernel of the two degeneracy pushforwards is preserved by the edge Hecke operator at $\ell$.
--
--   **The place above $q$.** $A_2$ is a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A_2$ (`hA₂`), the decomposition subgroup of $A_2$ over $\mathbb Q$ acts isometrically for the valuation of $A_2$ (`hiso₂`), and $v_2$ is a height-one prime of $\mathcal O_{\mathbb Q}$ containing $q$ (`hv₂`).
--
--   **The tower of $\overline{\mathbb Q}$-curves.** $F_N$ is a field, an algebra over $\overline{\mathbb Q}$ which is a curve over $\overline{\mathbb Q}$ in the sense of `IsCurveOver` (principal divisors exist with degree $0$, every place has residue field finite over $\overline{\mathbb Q}$, and the module of Kähler differentials is free of rank one) and of essentially finite type. The datum $\mathbb T$ is a $\mathtt{HeckeTower.TowerData}\ q\ q'\ F_N$: a family of fields $\mathbb T.F\,\ell$ indexed by the primes $\ell\notin\{q,q'\}$, each a curve over $\overline{\mathbb Q}$ of essentially finite type, together with, for each arrow $\alpha=(\ell,i)$ with $i\in\{0,1\}$, a $\overline{\mathbb Q}$-algebra map $\mathbb T.\varphi\,\alpha:F_N\to\mathbb T.F\,\ell$ that is finite and integral; the object $\mathrm{none}$ has field $F_N$ and the object $\mathrm{some}\ \ell$ has field $\mathbb T.F\,\ell$, and every arrow has codomain $\mathrm{none}$ and domain $\mathrm{some}\ \ell$. The hypothesis `hfg` requires each $\mathbb T.\mathrm{objField}\ j$ to contain an element $x$ transcendental over $\overline{\mathbb Q}$ such that $\mathbb T.\mathrm{objField}\ j$ is finite-dimensional over $\overline{\mathbb Q}(x)$. The homomorphisms $\mathrm{gal}_N:D\to\mathtt{SemilinearAut}(\overline{\mathbb Q},F_N)$ and $\mathrm{gal}_T\,\ell:D\to\mathtt{SemilinearAut}(\overline{\mathbb Q},\mathbb T.F\,\ell)$ take values in the group of pairs consisting of a ring automorphism of the function field and one of $\overline{\mathbb Q}$ that are compatible with the structure map; the hypotheses `hgalN` and `hgalT` say that the base automorphism of $\mathrm{gal}_N\,\tau$, respectively of $\mathrm{gal}_T\,\ell\,\tau$, is $\tau$ itself on $\overline{\mathbb Q}$. Finally $W:\{0,1\}\to\mathtt{SemilinearAut}(\overline{\mathbb Q},F_N)$ and $WT\,\ell:\{0,1\}\to\mathtt{SemilinearAut}(\overline{\mathbb Q},\mathbb T.F\,\ell)$ are two prescribed semilinear automorphisms at each level.
--
--   **Rigid-analytic data.** $\iota_2:H\to M_2(K_0)$ is an injective $\mathbb Q$-algebra map, and $\rho_2:H^\times\to\mathrm{PGL}_2(K_0)$ sends $x$ to the class of the matrix $\iota_2(x)$ (`hρ₂`). The element $\varpi_2$ is a pseudo-uniformiser of $K_0$ relative to $C$ (its image in $C$ has absolute value strictly between $0$ and $1$, and every nonzero element of $K_0$ is squeezed between two powers of it), and `hϖ₂` identifies the image of $\varpi_2$ in $C$ with $q$. The ring $\mathcal O$ is assumed to be a domain (`hdom₂`).
--
--   **Level-raising elements.** $s_2$ assigns to each prime $\ell\notin\{q,q'\}$ a unit of $H$ and $sf_2$ a unit of $H\otimes_{\mathbb Q}\mathbb A_f$; `hs₂` requires for each such $\ell$: the component of $sf_2\,\ell$ at every height-one prime $u$ not containing $q$ is $s_2\,\ell\otimes 1$; its component at every $u$ containing $q$ is $1$; the product of the diagonal idele of the central unit $\ell\in\mathbb Q^\times$ with $(sf_2\,\ell)^{-1}$ lies in $\mathtt{levelHeckeUSet}\ \Lambda_1\ S_1\ \ell$ when $\ell\mid N$ — that is, it lies in $\mathtt{primeHeckeSet}\ S_1\ \ell$, does not normalise $S_1$, and its conjugate of $\Lambda_1$ does not contain $S_1$ — and in $\mathtt{primeHeckeSet}\ S_1\ \ell$ otherwise; and $\mathrm{nrd}(s_2\,\ell)=\ell$, where $\mathrm{nrd}$ is the reduced norm $x\mapsto x_{\mathrm{re}}^2-a_1x_{I}^2-b_1x_{J}^2+a_1b_1x_{K}^2$.
--
--   **Level groups.** $\Gamma_2$ assigns a subgroup of $H^\times$ to each object of the tower; `hΓ₂0` characterises $\Gamma_2\,\mathrm{none}$ as the set of units $x$ lying in $\mathtt{awayUnits}\ R_1\ v_2$ — that is, for every height-one prime $w\neq v_2$ the image of $x$ in $(H\otimes_{\mathbb Q}\mathbb Q_w)^\times$ lies in the subgroup generated by the local box units of $R_1$ at $w$ — and such that $\mathrm{padicValRat}_q(\mathrm{nrd}\,x)$ is even; `hΓ₂ℓ` says $\Gamma_2(\mathrm{some}\ \ell)=\Gamma_2\,\mathrm{none}\cap s_2(\ell)\,\Gamma_2\,\mathrm{none}\,s_2(\ell)^{-1}$.
--
--   **Atkin–Lehner elements.** $w_2$ and $\bar w_2$ assign units of $H$ to the objects of the tower. The hypothesis `hw₂` requires $w_2\,\mathrm{none}\in\mathtt{awayUnits}\ R_1\ v_2$ with $\mathrm{nrd}(w_2\,\mathrm{none})=q$, and for each $\ell$ that $w_2(\mathrm{some}\ \ell)\in\mathtt{awayUnits}\ (\mathtt{meetOrder}\ R_1\ (sf_2\,\ell))\ v_2$ with reduced norm $q$. The hypothesis `hwbar₂` requires, for $\bar w_2\,\mathrm{none}$: reduced norm $q'$; for every height-one prime $u\neq v_2$ not containing $q'$, that the image of $\bar w_2\,\mathrm{none}$ in $(H\otimes_{\mathbb Q}\mathbb Q_u)^\times$ is a local box unit of $R_1$ at $u$; and for every $u\neq v_2$ and every $x\in H\otimes_{\mathbb Q}\mathbb Q_u$, that $\bar w^{-1}x\bar w$ lies in the local box of $R_1$ at $u$ if and only if $x$ does, and likewise with $\Lambda_1$ in place of $R_1$. The same three conditions are required of $\bar w_2(\mathrm{some}\ \ell)$ for each $\ell$, with $R_1$ replaced by $\mathtt{meetOrder}\ R_1\ (sf_2\,\ell)$ and with $\Lambda_1$ unchanged.
--
--   **Action on the completion, character, embeddings, intertwining.** $d_2$ is a homomorphism from $D$ to the group of isometric automorphisms of $C$ fixing $K_0$ pointwise, and `hdIso₂` says that the underlying ring automorphism of $d_2\,\tau$ is the action of $\tau$ on $C$. Further, $\chi_2:D\to\mathbb Z/2$ (written multiplicatively) is a character and $\iota M_2\,j:\mathbb T.\mathrm{objField}\ j\to\mathrm{Frac}(\mathcal O)$ a ring homomorphism for each object $j$. The last hypothesis `hI` is the predicate $\mathtt{DescentIntertwining}$ evaluated at $r=q$ and at the two distinguished indices $0$ and $1$, for the data $A_2,\rho_2,\varpi_2,\Gamma_2,w_2,\bar w_2,s_2,d_2,F_N,\mathbb T,\mathrm{gal}_N,\mathrm{gal}_T,W,WT,\chi_2,\iota M_2$. Among its clauses: $\chi_2$ is trivial on the image in $D$ of the inertia subgroup of $A_2$ over $\mathbb Q$; $\chi_2\varphi\neq1$ for every $\varphi\in D$ acting on the residue field of $A_2$ by $x\mapsto x^{q}$; $\chi_2\tau=1$ if and only if $\tau$ fixes every $x$ in the residue field of $A_2$ with $x^{q^2}=x$; and each $\iota M_2\,j$ carries a constant $z\in\overline{\mathbb Q}$ to the image of $z\in C$ in $\mathrm{Frac}(\mathcal O)$. Its remaining clauses relate the listed parameters to one another along the embeddings $\iota M_2\,j$.
--
--   **Conclusion.** Under these hypotheses there exist a type $S_2$ with a group structure, homomorphisms $\mathrm{scalar}_2:S_2\to D$ and $\iota S_2:D\to S_2$ with $\mathrm{scalar}_2(\iota S_2\,\tau)=\tau$ for all $\tau$, elements $\sigma_0,\sigma_1\in S_2$, a character $\chi S_2:S_2\to\mathbb Z/2$ (multiplicatively written), homomorphisms $\mathrm{gal}F_2\,j:S_2\to\mathtt{SemilinearAut}(\overline{\mathbb Q},\mathbb T.\mathrm{objField}\ j)$ and $\mathrm{gal}FC_2\,j:S_2\to\mathtt{SemilinearAut}(C,\mathcal M_j)$ for every object $j$, and a homomorphism $\mathrm{sgn}_2:S_2\to\mathbb Z^\times$, such that all of the following hold.
--
--   Structure of $S_2$: every $\sigma\in S_2$ can be written $\iota S_2(\tau)\,\sigma_0^{u}\,\sigma_1^{v}$ with $\tau\in D$ and $u,v$ natural numbers; $\mathrm{scalar}_2\sigma_0=1$ and $\mathrm{scalar}_2\sigma_1=1$; $\sigma_0^2=1$, $\sigma_1^2=1$, $\sigma_0\sigma_1=\sigma_1\sigma_0$, and both $\sigma_0$ and $\sigma_1$ commute with $\iota S_2\,\tau$ for every $\tau\in D$. Moreover $S_2$ has the corresponding universal property: for every group $H'$, every homomorphism $f:D\to H'$ and all $h_0,h_1\in H'$ with $h_0^2=h_1^2=1$, $h_0h_1=h_1h_0$ and $h_0,h_1$ commuting with every $f(\tau)$, there is a homomorphism $F:S_2\to H'$ with $F(\iota S_2\,\tau)=f(\tau)$ for all $\tau$, $F\sigma_0=h_0$ and $F\sigma_1=h_1$.
--
--   Action on the tower of $\overline{\mathbb Q}$-curves: for all $j$, $\sigma$ and $a\in\overline{\mathbb Q}$ the base automorphism of $\mathrm{gal}F_2\,j\,\sigma$ sends $a$ to $\mathrm{scalar}_2(\sigma)(a)$; $\mathrm{gal}F_2\,\mathrm{none}\,(\iota S_2\,\tau)=\mathrm{gal}_N\,\tau$ and $\mathrm{gal}F_2\,(\mathrm{some}\ \ell)\,(\iota S_2\,\tau)=\mathrm{gal}_T\,\ell\,\tau$ for all $\ell$ and $\tau$; for every arrow $\alpha$ of the tower, every $\sigma$ and every $x$ in the field at the codomain of $\alpha$, $\mathrm{gal}F_2(\mathrm{dom}\,\alpha)\,\sigma$ applied to $\mathbb T.\varphi\,\alpha\,(x)$ equals $\mathbb T.\varphi\,\alpha$ applied to $\mathrm{gal}F_2(\mathrm{cod}\,\alpha)\,\sigma\cdot x$; and $\mathrm{gal}F_2\,\mathrm{none}\,\sigma_0=W\,0$, $\mathrm{gal}F_2\,\mathrm{none}\,\sigma_1=W\,1$, while for every $\ell$ one has $\mathrm{gal}F_2(\mathrm{some}\ \ell)\,\sigma_0=WT\,\ell\,0$ and $\mathrm{gal}F_2(\mathrm{some}\ \ell)\,\sigma_1=WT\,\ell\,1$.
--
--   The character: $\chi S_2(\iota S_2\,\tau)=\chi_2\,\tau$ for all $\tau$, $\chi S_2\sigma_0\neq1$ and $\chi S_2\sigma_1=1$; $\chi S_2(\iota S_2\,\tau)=1$ whenever the automorphism underlying $\tau$ lies in the image in $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup of $A_2$; $\chi S_2(\iota S_2\,\varphi)\neq1$ for every $\varphi\in D$ that is a Frobenius at $q$ for $A_2$ (acting as $x\mapsto x^{q}$ on the residue field); and $\chi S_2(\iota S_2\,\tau)=1$ if and only if $\tau$ fixes every $x$ in the residue field of $A_2$ with $x^{q^{2}}=x$.
--
--   Action on the Mumford invariant fields: for all $j$, $\sigma$ and $c\in C$ the base automorphism of $\mathrm{gal}FC_2\,j\,\sigma$ sends $c$ to $\mathrm{scalar}_2(\sigma)\cdot c$, and also to the image of $c$ under the ring automorphism underlying $d_2(\mathrm{scalar}_2\sigma)$; the base automorphisms of $\mathrm{gal}FC_2\,j\,\sigma_0$ and of $\mathrm{gal}FC_2\,j\,\sigma_1$ are the identity on $C$. Compatibility with the embeddings: for all $j$, $\sigma$, $x\in\mathbb T.\mathrm{objField}\ j$ and $y\in\mathcal M_j$ with $y=\iota M_2\,j\,(x)$ in $\mathrm{Frac}(\mathcal O)$, one has $\mathrm{gal}FC_2\,j\,\sigma\cdot y=\iota M_2\,j\,(\mathrm{gal}F_2\,j\,\sigma\cdot x)$ in $\mathrm{Frac}(\mathcal O)$. Explicit formulae: for $\tau\in D$, $j$ and $y\in\mathcal M_j$, the element $\mathrm{gal}FC_2\,j\,(\iota S_2\,\tau)\cdot y$ equals, inside $\mathrm{Frac}(\mathcal O)$, the result of applying to $y$ the coefficientwise extension of $d_2\,\tau$ to $\mathrm{Frac}(\mathcal O)$ and then acting by $1$ if $\chi_2\,\tau=1$ and by $w_2\,j$ otherwise; $\mathrm{gal}FC_2\,j\,\sigma_0\cdot y=w_2\,j\cdot y$ and $\mathrm{gal}FC_2\,j\,\sigma_1\cdot y=\bar w_2\,j\cdot y$ in $\mathrm{Frac}(\mathcal O)$.
--
--   Shape of the action and the sign: for every $j$ and $\sigma$ there exist $n\in H^\times$ normalising $\Gamma_2\,j$ and an isometric automorphism $t$ of $C$ over $K_0$ such that $\mathrm{gal}FC_2\,j\,\sigma\cdot y=n\cdot(\text{coefficientwise extension of }t)(y)$ for every $y\in\mathcal M_j$; and, with $t$ prescribed, for every $j$ and $\sigma$ there exists $n\in H^\times$ normalising $\Gamma_2\,j$ such that $\mathrm{sgn}_2\sigma=1$ if and only if $\mathrm{padicValRat}_q(\mathrm{nrd}\,n)$ is even, and $\mathrm{gal}FC_2\,j\,\sigma\cdot y=n\cdot(\text{coefficientwise extension of }d_2(\mathrm{scalar}_2\sigma))(y)$ for every $y\in\mathcal M_j$. Furthermore $\mathrm{sgn}_2(\iota S_2\,\tau)=1$ whenever $\chi S_2(\iota S_2\,\tau)=1$, $\mathrm{sgn}_2(\iota S_2\,\tau)=\mathrm{sgn}_2\sigma_0$ whenever $\chi S_2(\iota S_2\,\tau)\neq1$, and $\mathrm{sgn}_2\sigma_0=-1$, $\mathrm{sgn}_2\sigma_1=1$.
--
--   Finally, compatibility with the degeneracy maps on the analytic side: for every arrow $\alpha$ of the tower, every $\sigma\in S_2$ and every $C$-algebra map $\varphi^C:\mathcal M_{\mathrm{cod}\,\alpha}\to\mathcal M_{\mathrm{dom}\,\alpha}$ which in $\mathrm{Frac}(\mathcal O)$ is given by acting by $1$ if the second component of $\alpha$ is $0$ and by $s_2(\alpha.1)$ otherwise, one has $\mathrm{gal}FC_2(\mathrm{dom}\,\alpha)\,\sigma\cdot\varphi^C(x)=\varphi^C(\mathrm{gal}FC_2(\mathrm{cod}\,\alpha)\,\sigma\cdot x)$ for all $x$.
--
--   This is the construction, at a place $A_2$ of $\overline{\mathbb Q}$ above $q$, of the symmetry group of the Čerednik–Drinfeld situation: the decomposition group at $A_2$ extended by two commuting involutions, the Atkin–Lehner involution at $q$ and the one at $q'$, acting compatibly on the abstract Hecke tower of $\overline{\mathbb Q}$-curves and, through the embeddings into the fraction field of the ring of holomorphic functions on Drinfeld's upper half-plane, on the $\Gamma_2\,j$-invariant fields, with the sign character recording the parity of the $q$-valuation of the reduced norm of the normalising element. It is used by [`CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero), where the Shimura-curve tower is matched with its equivariant $p$-adic uniformisation; the proof rests on [`CerednikDrinfeld.CosetGraph.atkinLehner_relations_levelGroups_place`](thm.html#CerednikDrinfeld.CosetGraph.atkinLehner_relations_levelGroups_place) for the Atkin–Lehner relations between the level groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_zero_one.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

theorem CerednikDrinfeld.exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_zero_one

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
      FN 𝕋 galN galT W WT χ₂ ιM₂) :
    ∃ (S₂ : Type) (_ : Group S₂) (scalar₂ : S₂ →* ↥(A₂.decompositionSubgroup ℚ))
      (ιS₂ : ↥(A₂.decompositionSubgroup ℚ) →* S₂) (_ : ∀ τ, scalar₂ (ιS₂ τ) = τ)

      (σ₀₂ σ₁₂ : S₂)
      (χS₂ : S₂ →* Multiplicative (ZMod 2))

      (galF₂ : ∀ j : HeckeTower.Obj q q', S₂ →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.objField j))

      (galFC₂ : ∀ j : HeckeTower.Obj q q',
        S₂ →* SemilinearAut A₂.valuation.Completion ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j)))

      (sgn₂ : S₂ →* ℤˣ),

      (∀ σ : S₂, ∃ (τ : ↥(A₂.decompositionSubgroup ℚ)) (u v : ℕ), σ = ιS₂ τ * σ₀₂ ^ u * σ₁₂ ^ v) ∧
      scalar₂ σ₀₂ = 1 ∧ scalar₂ σ₁₂ = 1 ∧ σ₀₂ * σ₀₂ = 1 ∧ σ₁₂ * σ₁₂ = 1 ∧
      σ₀₂ * σ₁₂ = σ₁₂ * σ₀₂ ∧ (∀ τ, ιS₂ τ * σ₀₂ = σ₀₂ * ιS₂ τ) ∧ (∀ τ, ιS₂ τ * σ₁₂ = σ₁₂ * ιS₂ τ) ∧

      (∀ (H : Type) [Group H] (f : ↥(A₂.decompositionSubgroup ℚ) →* H) (h₀ h₁ : H),
        h₀ * h₀ = 1 → h₁ * h₁ = 1 → h₀ * h₁ = h₁ * h₀ → (∀ τ, f τ * h₀ = h₀ * f τ) → (∀ τ, f τ * h₁ = h₁ * f τ) →
        ∃ F : S₂ →* H, (∀ τ, F (ιS₂ τ) = f τ) ∧ F σ₀₂ = h₀ ∧ F σ₁₂ = h₁) ∧

      (∀ j (σ : S₂) (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (galF₂ j σ) a =
        ((scalar₂ σ : ↥(A₂.decompositionSubgroup ℚ)) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a) ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ), galF₂ none (ιS₂ τ) = galN τ) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (τ : ↥(A₂.decompositionSubgroup ℚ)), galF₂ (some ℓ) (ιS₂ τ) = galT ℓ τ) ∧
      (∀ (α : HeckeTower.Arr q q') (σ : S₂) (x : 𝕋.objField (HeckeTower.cod α)),
        galF₂ (HeckeTower.dom α) σ • (show 𝕋.objField (HeckeTower.dom α) from 𝕋.φ α x) =
          (show 𝕋.objField (HeckeTower.dom α) from 𝕋.φ α (galF₂ (HeckeTower.cod α) σ • x))) ∧
      galF₂ none σ₀₂ = W 0 ∧ galF₂ none σ₁₂ = W 1 ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', galF₂ (some ℓ) σ₀₂ = WT ℓ 0 ∧ galF₂ (some ℓ) σ₁₂ = WT ℓ 1) ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ), χS₂ (ιS₂ τ) = χ₂ τ) ∧ χS₂ σ₀₂ ≠ 1 ∧ χS₂ σ₁₂ = 1 ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ),
        (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₂.inertiaSubgroupIn ℚ → χS₂ (ιS₂ τ) = 1) ∧
      (∀ φ : ↥(A₂.decompositionSubgroup ℚ),
        A₂.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q → χS₂ (ιS₂ φ) ≠ 1) ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ), χS₂ (ιS₂ τ) = 1 ↔
        ∀ x : IsLocalRing.ResidueField ↥A₂, x ^ (q ^ 2) = x → τ • x = x) ∧

      (∀ j (σ : S₂) (c : A₂.valuation.Completion),
        SemilinearAut.baseAut (galFC₂ j σ) c = (scalar₂ σ) • c) ∧
      (∀ j (σ : S₂) (c : A₂.valuation.Completion),
        SemilinearAut.baseAut (galFC₂ j σ) c = (dIso₂ (scalar₂ σ)).toRingEquiv c) ∧
      (∀ j (c : A₂.valuation.Completion), SemilinearAut.baseAut (galFC₂ j σ₀₂) c = c) ∧
      (∀ j (c : A₂.valuation.Completion), SemilinearAut.baseAut (galFC₂ j σ₁₂) c = c) ∧
      (∀ j (σ : S₂) (x : 𝕋.objField j) (y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))),
        (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = ιM₂ j x →
          ((galFC₂ j σ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = ιM₂ j (galF₂ j σ • x)) ∧
      (∀ j (τ : ↥(A₂.decompositionSubgroup ℚ)) (y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))),
        ((galFC₂ j (ιS₂ τ) • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
          (if χ₂ τ = 1 then (1 : (ℍ[ℚ, a₁, b₁])ˣ) else w₂ j) •
            Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ (dIso₂ τ)) (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧
      (∀ j (y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))),
        ((galFC₂ j σ₀₂ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = (w₂ j) • (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧
      (∀ j (y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))),
        ((galFC₂ j σ₁₂ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = (wbar₂ j) • (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧

      (∀ j (σ : S₂), ∃ (n : (ℍ[ℚ, a₁, b₁])ˣ) (t : Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion),
        n ∈ Subgroup.normalizer ((Γ₂ j : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) : Set (ℍ[ℚ, a₁, b₁])ˣ) ∧
        ∀ y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j)),
          ((galFC₂ j σ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ t) (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧

      (∀ j (σ : S₂), ∃ n : (ℍ[ℚ, a₁, b₁])ˣ,
        n ∈ Subgroup.normalizer ((Γ₂ j : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) : Set (ℍ[ℚ, a₁, b₁])ˣ) ∧ (sgn₂ σ = 1 ↔ Even (padicValRat q (nrd (n : ℍ[ℚ, a₁, b₁])))) ∧
        ∀ y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j)),
          ((galFC₂ j σ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ (dIso₂ (scalar₂ σ))) (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ), χS₂ (ιS₂ τ) = 1 → sgn₂ (ιS₂ τ) = 1) ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ), χS₂ (ιS₂ τ) ≠ 1 → sgn₂ (ιS₂ τ) = sgn₂ σ₀₂) ∧
      sgn₂ σ₀₂ = -1 ∧ sgn₂ σ₁₂ = 1 ∧
      (∀ (α : HeckeTower.Arr q q') (σ : S₂)
        (φC : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ (HeckeTower.cod α))) →ₐ[A₂.valuation.Completion] ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ (HeckeTower.dom α)))),
        (∀ x, (φC x : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = (if α.2 = 0 then (1 : (ℍ[ℚ, a₁, b₁])ˣ) else s₂ α.1) • (x : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) →
        ∀ x, galFC₂ (HeckeTower.dom α) σ • φC x = φC (galFC₂ (HeckeTower.cod α) σ • x)) := by sorry
