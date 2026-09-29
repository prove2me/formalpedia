-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero
-- name    : CerednikDrinfeld.exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/f44bee1d-a3d1-597a-8d86-506654cf8842
-- title:
--   Symmetry group with compatible semilinear actions over q'
-- statement:
--   Throughout, write $H := \mathbb{H}[\mathbb{Q},a_2,b_2]$ for the quaternion algebra attached to $a_2,b_2\in\mathbb{Q}$, $\mathbb{A}_f$ for the finite adele ring of $\mathbb{Q}$, $C := A_1.\mathrm{valuation.Completion}$ for the completion of $\overline{\mathbb{Q}}$ at the valuation subring $A_1$, $K_0 := \verb|ValuationSubring.ratClosure| A_1$ for the topological closure of the prime subfield inside $C$, $D := A_1.\mathrm{decompositionSubgroup}\,\mathbb{Q}$ for the decomposition subgroup of $A_1$ inside $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$, $M := \verb|Omega.HolRingOf| \varpi_1\,\rho_1$ for the ring of functions on Drinfeld's upper half plane that are holomorphic on every affinoid of the $\varpi_1$-exhaustion, and, for each level $j$, $\mathcal{M}_j := \verb|Mumford.invariantFieldOf| C\,H^\times M\,(\Gamma_1 j)$ for the subfield of $\mathrm{Frac}(M)$ of elements fixed by every element of $\Gamma_1 j$. The index types are $\verb|HeckeTower.AwayPrime| q\,q' = \{\ell \text{ prime} : \ell \neq q,\ \ell \neq q'\}$, $\verb|Obj| q\,q' = \mathrm{Option}(\verb|AwayPrime| q\,q')$ and $\verb|Arr| q\,q' = \verb|AwayPrime| q\,q' \times \mathrm{Fin}\,2$, with $\mathrm{dom}\,\alpha = \mathrm{some}\,\alpha_1$ and $\mathrm{cod}\,\alpha = \mathrm{none}$; $\verb|SemilinearAut| K\,F$ is the group of pairs $(\text{ring automorphism of }F,\ \text{ring automorphism of }K)$ compatible with the structure map, and $\verb|baseAut|$ is its second component.
--
--   *Quaternionic data.* Natural numbers $N$ (nonzero and squarefree, `hN`), $q$ and $q'$ prime with $q \nmid N$, $q' \nmid N$, $q' \neq q$, $5 \le q$ and $5 \le q'$. The hypothesis `hdef₂` requires $a_2 < 0$, $b_2 < 0$ and that, for a finite place $v$ of $\mathbb{Q}$, every nonzero element of $H \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $q \in v$. Further, $\mathbb{Z}$-submodules $\Lambda_2, R_2 \subseteq H$ with $\Lambda_2$ a maximal order (an order maximal among the orders containing it), $R_2$ an Eichler order of level $N$ (an intersection of two maximal orders whose relative index in the first is $N$) and $R_2 \le \Lambda_2$; a unit $n_2 \in (H \otimes_{\mathbb{Q}} \mathbb{A}_f)^\times$ lying in $\verb|primeHeckeSet| R_2\,q'$, i.e. $n_2$ lies in the adelic box of $R_2$, $q'\,n_2^{-1}$ lies in that box, while $n_2^{-1}$ and $q'^{-1} n_2$ do not. Setting $S_2 := \verb|meetOrder| R_2\,n_2 = R_2 \cap \verb|conjByFiniteIdele| R_2\,n_2$, the hypotheses require: $S_2$ is an Eichler order of level $Nq'$ (`hS₂`); $\verb|conjByFiniteIdele| S_2\,n_2 = S_2$ (`hnorm₂`); the shift $x \mapsto [\,x^{\mathrm{out}} n_2\,]$ on the class set of the finite-idele stabiliser of $S_2$ is an involution (`hsq₂`); and `hlaws₂`, the conjunction `ClassSetHeckeLaws N q' Λ₂ R₂ n₂` of four clauses: the edge Hecke matrices at all primes commute pairwise, the vertex Hecke matrices at all primes commute pairwise, for every prime $\ell \neq q$ and each of the two degeneracy pushforwards the edge Hecke operator is intertwined with the vertex Hecke operator, and the joint kernel of the two pushforwards is stable under every edge Hecke operator.
--
--   *Place and tower data.* A valuation subring $A_1$ of $\overline{\mathbb{Q}}$ with $q'$ in its nonunits (`hA₁`), satisfying the standing assumption that every element of $D$ preserves the valuation of $A_1$; a height-one prime $v_1$ of $\mathcal{O}_{\mathbb{Q}}$ containing $q'$. A field $FN$ over $\overline{\mathbb{Q}}$ which is a curve over $\overline{\mathbb{Q}}$ (principal divisors of degree zero exist, all residue fields at places are finite over $\overline{\mathbb{Q}}$, and the module of Kähler differentials is free of rank one) and of essentially finite type; tower data $\mathbb{T}$ of type `HeckeTower.TowerData q q' FN`, consisting of curve fields $\mathbb{T}.F\ell$ over $\overline{\mathbb{Q}}$ for $\ell$ away from $q,q'$ together with finite integral $\overline{\mathbb{Q}}$-algebra maps $\mathbb{T}.\varphi\alpha : FN \to \mathbb{T}.F\alpha_1$ for each arrow $\alpha$; and `hfg`, asserting that each field $\mathbb{T}.\mathrm{objField}\,j$ ($FN$ for $j = \mathrm{none}$, $\mathbb{T}.F\ell$ for $j = \mathrm{some}\,\ell$) contains an element transcendental over $\overline{\mathbb{Q}}$ over whose adjoined subfield it is finite-dimensional. Semilinear actions $\mathrm{gal}N : D \to \verb|SemilinearAut| \overline{\mathbb{Q}}\,FN$ and $\mathrm{gal}T\,\ell : D \to \verb|SemilinearAut| \overline{\mathbb{Q}}\,(\mathbb{T}.F\ell)$ whose base automorphisms are the given Galois elements (`hgalN`, `hgalT`), and prescribed candidate involutions $W : \mathrm{Fin}\,2 \to \verb|SemilinearAut| \overline{\mathbb{Q}}\,FN$ and $WT\,\ell : \mathrm{Fin}\,2 \to \verb|SemilinearAut| \overline{\mathbb{Q}}\,(\mathbb{T}.F\ell)$.
--
--   *Mumford-side data.* An injective $\mathbb{Q}$-algebra map $\iota_1 : H \to M_2(K_0)$ and a homomorphism $\rho_1 : H^\times \to \mathrm{PGL}_2(K_0)$ induced by $\iota_1$ (`hρ₁`); a pseudo-uniformiser $\varpi_1$ of $K_0$ in $C$ whose image in $C$ is $q'$ (`hϖ₁`), with $M$ a domain. Level-raising elements $s_1 : \verb|AwayPrime| q\,q' \to H^\times$ and $sf_1$ with values in $(H \otimes_{\mathbb{Q}} \mathbb{A}_f)^\times$ satisfying `hs₁`: for each $\ell$, the component of $sf_1\ell$ at every finite place $u$ not containing $q'$ is $s_1\ell \otimes 1$, its component at every $u$ containing $q'$ is $1$, the product of the diagonal idele of the scalar $\ell$ with $(sf_1\ell)^{-1}$ lies in $\verb|levelHeckeUSet| \Lambda_2\,S_2\,\ell$ when $\ell \mid N$ (that is, in the $\ell$-th prime Hecke set of $S_2$, with $\verb|conjByFiniteIdele| S_2$ by the element distinct from $S_2$ and $S_2$ not contained in the corresponding conjugate of $\Lambda_2$) and in $\verb|primeHeckeSet| S_2\,\ell$ otherwise, and $\mathrm{nrd}(s_1\ell) = \ell$. Level groups $\Gamma_1 : \verb|Obj| q\,q' \to$ subgroups of $H^\times$ with $\Gamma_1(\mathrm{none})$ the set of units lying in $\verb|CosetGraph.awayUnits| R_2\,v_1$ (units whose image at each place $w \neq v_1$ lies in the subgroup generated by the local box units of $R_2$ at $w$) whose reduced norm has even $q'$-adic valuation (`hΓ₁0`), and $\Gamma_1(\mathrm{some}\,\ell) = \Gamma_1(\mathrm{none}) \cap s_1\ell\,\Gamma_1(\mathrm{none})\,(s_1\ell)^{-1}$ (`hΓ₁ℓ`). Atkin–Lehner elements $w_1, \bar w_1 : \verb|Obj| q\,q' \to H^\times$ with `hw₁`: $w_1(\mathrm{none})$ lies in $\verb|awayUnits| R_2\,v_1$ and has reduced norm $q'$, and $w_1(\mathrm{some}\,\ell)$ lies in $\verb|awayUnits| (\verb|meetOrder| R_2\,(sf_1\ell))\,v_1$ and has reduced norm $q'$; and `hwbar₁`: for $j = \mathrm{none}$ with the order $R_2$, and for $j = \mathrm{some}\,\ell$ with the order $\verb|meetOrder| R_2\,(sf_1\ell)$, the element $\bar w_1 j$ has reduced norm $q$, its local image at every $u \neq v_1$ not containing $q$ is a local box unit of that order, and conjugation by its local image at every $u \neq v_1$ preserves both the local box of that order and the local box of $\Lambda_2$. Finally, a homomorphism $d_1 : D \to \verb|Omega.IsometricAut| K_0\,C$ whose underlying ring isomorphism is the Galois action on $C$ (`hdIso₁`), a character $\chi_1 : D \to \mathrm{Multiplicative}(\mathbb{Z}/2)$, ring homomorphisms $\iota M_1 j : \mathbb{T}.\mathrm{objField}\,j \to \mathrm{Frac}(M)$, and the hypothesis `hI` that all this data satisfies the predicate [`CerednikDrinfeld.DescentIntertwining`](def/CerednikDrinfeld_DescentIntertwining_v2.html#L17) with parameters $r = q'$ and indices $1$ and $0$; among its clauses are that $\chi_1$ is trivial on the inertia subgroup of $A_1$ over $\mathbb{Q}$, that $\chi_1 \varphi \neq 1$ for every Frobenius element at $q'$, that $\chi_1 \tau = 1$ holds exactly when $\tau$ fixes every element $x$ of the residue field of $A_1$ with $x^{q'^2} = x$, and that each $\iota M_1 j$ carries constants from $\overline{\mathbb{Q}}$ to constants from $C$, together with the remaining intertwining conditions relating $\iota M_1$ to $\mathrm{gal}N$, $\mathrm{gal}T$, $W$, $WT$, $d_1$, the $\Gamma_1 j$, the Atkin–Lehner elements $w_1, \bar w_1$ and the degeneracy elements $s_1$.
--
--   *Conclusion.* There exist a type $S_1$ with a group structure, homomorphisms $\mathrm{scalar}_1 : S_1 \to D$ and $\iota S_1 : D \to S_1$ with $\mathrm{scalar}_1(\iota S_1 \tau) = \tau$ for all $\tau$, elements $\sigma_{01}, \sigma_{11} \in S_1$, a character $\chi S_1 : S_1 \to \mathrm{Multiplicative}(\mathbb{Z}/2)$, semilinear actions $\mathrm{galF}_1 j : S_1 \to \verb|SemilinearAut| \overline{\mathbb{Q}}\,(\mathbb{T}.\mathrm{objField}\,j)$ and $\mathrm{galFC}_1 j : S_1 \to \verb|SemilinearAut| C\,\mathcal{M}_j$ for every level $j$, and a sign homomorphism $\mathrm{sgn}_1 : S_1 \to \mathbb{Z}^\times$, such that all of the following hold.
--
--   Group structure: every $\sigma \in S_1$ can be written as $\iota S_1 \tau \cdot \sigma_{01}^u \cdot \sigma_{11}^v$ with $\tau \in D$ and $u, v \in \mathbb{N}$; $\mathrm{scalar}_1 \sigma_{01} = \mathrm{scalar}_1 \sigma_{11} = 1$; $\sigma_{01}^2 = \sigma_{11}^2 = 1$; $\sigma_{01}$ and $\sigma_{11}$ commute with each other and each commutes with $\iota S_1 \tau$ for every $\tau \in D$. Universal property: for every group $H'$, homomorphism $f : D \to H'$ and elements $h_0, h_2 \in H'$ with $h_0^2 = h_2^2 = 1$, $h_0 h_2 = h_2 h_0$ and both commuting with all $f\tau$, there is a homomorphism $F : S_1 \to H'$ with $F(\iota S_1 \tau) = f\tau$ for all $\tau$, $F\sigma_{01} = h_0$ and $F\sigma_{11} = h_2$.
--
--   Action on the $\overline{\mathbb{Q}}$-tower: for every $j$, $\sigma$ and $a \in \overline{\mathbb{Q}}$, the base automorphism of $\mathrm{galF}_1 j\,\sigma$ sends $a$ to $(\mathrm{scalar}_1 \sigma)(a)$; $\mathrm{galF}_1 \mathrm{none} \circ \iota S_1 = \mathrm{gal}N$ and $\mathrm{galF}_1 (\mathrm{some}\,\ell) \circ \iota S_1 = \mathrm{gal}T\,\ell$ for every $\ell$; for every arrow $\alpha$, every $\sigma$ and every $x$ in the field at $\mathrm{cod}\,\alpha$, one has $\mathrm{galF}_1(\mathrm{dom}\,\alpha)\sigma \cdot (\mathbb{T}.\varphi\alpha\,x) = \mathbb{T}.\varphi\alpha(\mathrm{galF}_1(\mathrm{cod}\,\alpha)\sigma \cdot x)$; and $\mathrm{galF}_1 \mathrm{none}\,\sigma_{01} = W 1$, $\mathrm{galF}_1 \mathrm{none}\,\sigma_{11} = W 0$, while $\mathrm{galF}_1(\mathrm{some}\,\ell)\sigma_{01} = WT\ell\,1$ and $\mathrm{galF}_1(\mathrm{some}\,\ell)\sigma_{11} = WT\ell\,0$ for every $\ell$.
--
--   The character: $\chi S_1 \circ \iota S_1 = \chi_1$, $\chi S_1 \sigma_{01} \neq 1$, $\chi S_1 \sigma_{11} = 1$; $\chi S_1(\iota S_1 \tau) = 1$ whenever the image of $\tau$ lies in the inertia subgroup of $A_1$ over $\mathbb{Q}$; $\chi S_1(\iota S_1 \varphi) \neq 1$ for every $\varphi$ that is a Frobenius element of $A_1$ at $q'$; and $\chi S_1(\iota S_1 \tau) = 1$ if and only if $\tau$ fixes every element $x$ of the residue field of $A_1$ with $x^{q'^2} = x$.
--
--   Action on the Mumford quotient fields: for every $j$, $\sigma$ and $c \in C$, the base automorphism of $\mathrm{galFC}_1 j\,\sigma$ sends $c$ to $(\mathrm{scalar}_1\sigma) \cdot c$, and equally to $d_1(\mathrm{scalar}_1\sigma)(c)$; the base automorphisms of $\mathrm{galFC}_1 j\,\sigma_{01}$ and $\mathrm{galFC}_1 j\,\sigma_{11}$ are the identity on $C$. Compatibility with $\iota M_1$: for every $j$, $\sigma$, $x \in \mathbb{T}.\mathrm{objField}\,j$ and $y \in \mathcal{M}_j$ with $y = \iota M_1 j\,x$ in $\mathrm{Frac}(M)$, one has $\mathrm{galFC}_1 j\,\sigma \cdot y = \iota M_1 j(\mathrm{galF}_1 j\,\sigma \cdot x)$ in $\mathrm{Frac}(M)$. Explicit formulae: for every $j$, $\tau \in D$ and $y \in \mathcal{M}_j$, $\mathrm{galFC}_1 j(\iota S_1 \tau) \cdot y$ equals, inside $\mathrm{Frac}(M)$, the action of $1$ if $\chi_1 \tau = 1$ and of $w_1 j$ otherwise on $\verb|fracMap|(\verb|toAmbientOf| \varpi_1\,\rho_1\,(d_1\tau))(y)$; moreover $\mathrm{galFC}_1 j\,\sigma_{01} \cdot y = w_1 j \cdot y$ and $\mathrm{galFC}_1 j\,\sigma_{11} \cdot y = \bar w_1 j \cdot y$ in $\mathrm{Frac}(M)$.
--
--   Normalizer descriptions and the sign: for every $j$ and $\sigma$ there are $n \in H^\times$ in the normalizer of $\Gamma_1 j$ and an isometric automorphism $t$ of $C$ over $K_0$ such that $\mathrm{galFC}_1 j\,\sigma \cdot y = n \cdot \verb|fracMap|(\verb|toAmbientOf| \varpi_1\,\rho_1\,t)(y)$ for all $y \in \mathcal{M}_j$; and for every $j$ and $\sigma$ there is $n \in H^\times$ in the normalizer of $\Gamma_1 j$ with $\mathrm{sgn}_1 \sigma = 1$ if and only if the $q'$-adic valuation of $\mathrm{nrd}(n)$ is even, such that $\mathrm{galFC}_1 j\,\sigma \cdot y = n \cdot \verb|fracMap|(\verb|toAmbientOf| \varpi_1\,\rho_1\,(d_1(\mathrm{scalar}_1\sigma)))(y)$ for all $y \in \mathcal{M}_j$. Furthermore $\mathrm{sgn}_1(\iota S_1\tau) = 1$ whenever $\chi S_1(\iota S_1 \tau) = 1$, $\mathrm{sgn}_1(\iota S_1 \tau) = \mathrm{sgn}_1 \sigma_{01}$ whenever $\chi S_1(\iota S_1 \tau) \neq 1$, and $\mathrm{sgn}_1 \sigma_{01} = -1$, $\mathrm{sgn}_1 \sigma_{11} = 1$.
--
--   Compatibility with the degeneracy maps: for every arrow $\alpha$, every $\sigma \in S_1$ and every $C$-algebra map $\varphi^C : \mathcal{M}_{\mathrm{cod}\,\alpha} \to \mathcal{M}_{\mathrm{dom}\,\alpha}$ which on $\mathrm{Frac}(M)$ is given by multiplication by $1$ if $\alpha_2 = 0$ and by the action of $s_1 \alpha_1$ otherwise, one has $\mathrm{galFC}_1(\mathrm{dom}\,\alpha)\sigma \cdot \varphi^C(x) = \varphi^C(\mathrm{galFC}_1(\mathrm{cod}\,\alpha)\sigma \cdot x)$ for all $x$.
--
--   This packages the decomposition group at a place of $\overline{\mathbb{Q}}$ above $q'$ together with the two Atkin–Lehner involutions (at $q'$ and at $q$) into a single group acting semilinearly and compatibly both on an abstract Hecke tower of $\overline{\mathbb{Q}}$-curves and on the Mumford quotient function fields of Drinfeld's upper half plane, in the setting of the Čerednik–Drinfeld uniformisation of Shimura curves. It is used by [`CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero), where the semilinear action, its scalar law, its transport along the maps $\iota M_1$ and its commutation with the degeneracy maps are the input to the comparison of models with their equivariant analytic uniformisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero.lean

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

theorem CerednikDrinfeld.exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero

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
      FN 𝕋 galN galT W WT χ₁ ιM₁) :
∃ (S₁ : Type) (_ : Group S₁) (scalar₁ : S₁ →* ↥(A₁.decompositionSubgroup ℚ))
      (ιS₁ : ↥(A₁.decompositionSubgroup ℚ) →* S₁) (_ : ∀ τ, scalar₁ (ιS₁ τ) = τ)

      (σ₀₁ σ₁₁ : S₁)
      (χS₁ : S₁ →* Multiplicative (ZMod 2))

      (galF₁ : ∀ j : HeckeTower.Obj q q', S₁ →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.objField j))

      (galFC₁ : ∀ j : HeckeTower.Obj q q',
        S₁ →* SemilinearAut A₁.valuation.Completion ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)))

      (sgn₁ : S₁ →* ℤˣ),

      (∀ σ : S₁, ∃ (τ : ↥(A₁.decompositionSubgroup ℚ)) (u v : ℕ), σ = ιS₁ τ * σ₀₁ ^ u * σ₁₁ ^ v) ∧
      scalar₁ σ₀₁ = 1 ∧ scalar₁ σ₁₁ = 1 ∧ σ₀₁ * σ₀₁ = 1 ∧ σ₁₁ * σ₁₁ = 1 ∧
      σ₀₁ * σ₁₁ = σ₁₁ * σ₀₁ ∧ (∀ τ, ιS₁ τ * σ₀₁ = σ₀₁ * ιS₁ τ) ∧ (∀ τ, ιS₁ τ * σ₁₁ = σ₁₁ * ιS₁ τ) ∧

      (∀ (H : Type) [Group H] (f : ↥(A₁.decompositionSubgroup ℚ) →* H) (h₀ h₂ : H),
        h₀ * h₀ = 1 → h₂ * h₂ = 1 → h₀ * h₂ = h₂ * h₀ → (∀ τ, f τ * h₀ = h₀ * f τ) → (∀ τ, f τ * h₂ = h₂ * f τ) →
        ∃ F : S₁ →* H, (∀ τ, F (ιS₁ τ) = f τ) ∧ F σ₀₁ = h₀ ∧ F σ₁₁ = h₂) ∧

      (∀ j (σ : S₁) (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (galF₁ j σ) a =
        ((scalar₁ σ : ↥(A₁.decompositionSubgroup ℚ)) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), galF₁ none (ιS₁ τ) = galN τ) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (τ : ↥(A₁.decompositionSubgroup ℚ)), galF₁ (some ℓ) (ιS₁ τ) = galT ℓ τ) ∧
      (∀ (α : HeckeTower.Arr q q') (σ : S₁) (x : 𝕋.objField (HeckeTower.cod α)),
        galF₁ (HeckeTower.dom α) σ • (show 𝕋.objField (HeckeTower.dom α) from 𝕋.φ α x) =
          (show 𝕋.objField (HeckeTower.dom α) from 𝕋.φ α (galF₁ (HeckeTower.cod α) σ • x))) ∧
      galF₁ none σ₀₁ = W 1 ∧ galF₁ none σ₁₁ = W 0 ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', galF₁ (some ℓ) σ₀₁ = WT ℓ 1 ∧ galF₁ (some ℓ) σ₁₁ = WT ℓ 0) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) = χ₁ τ) ∧ χS₁ σ₀₁ ≠ 1 ∧ χS₁ σ₁₁ = 1 ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ),
        (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₁.inertiaSubgroupIn ℚ → χS₁ (ιS₁ τ) = 1) ∧
      (∀ φ : ↥(A₁.decompositionSubgroup ℚ),
        A₁.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q' → χS₁ (ιS₁ φ) ≠ 1) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) = 1 ↔
        ∀ x : IsLocalRing.ResidueField ↥A₁, x ^ (q' ^ 2) = x → τ • x = x) ∧

      (∀ j (σ : S₁) (c : A₁.valuation.Completion),
        SemilinearAut.baseAut (galFC₁ j σ) c = (scalar₁ σ) • c) ∧
      (∀ j (σ : S₁) (c : A₁.valuation.Completion),
        SemilinearAut.baseAut (galFC₁ j σ) c = (dIso₁ (scalar₁ σ)).toRingEquiv c) ∧
      (∀ j (c : A₁.valuation.Completion), SemilinearAut.baseAut (galFC₁ j σ₀₁) c = c) ∧
      (∀ j (c : A₁.valuation.Completion), SemilinearAut.baseAut (galFC₁ j σ₁₁) c = c) ∧
      (∀ j (σ : S₁) (x : 𝕋.objField j) (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = ιM₁ j x →
          ((galFC₁ j σ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = ιM₁ j (galF₁ j σ • x)) ∧
      (∀ j (τ : ↥(A₁.decompositionSubgroup ℚ)) (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        ((galFC₁ j (ιS₁ τ) • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
          (if χ₁ τ = 1 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else w₁ j) •
            Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ τ)) (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧
      (∀ j (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        ((galFC₁ j σ₀₁ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = (w₁ j) • (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧
      (∀ j (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        ((galFC₁ j σ₁₁ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = (wbar₁ j) • (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧

      (∀ j (σ : S₁), ∃ (n : (ℍ[ℚ, a₂, b₂])ˣ) (t : Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion),
        n ∈ Subgroup.normalizer ((Γ₁ j : Subgroup (ℍ[ℚ, a₂, b₂])ˣ) : Set (ℍ[ℚ, a₂, b₂])ˣ) ∧
        ∀ y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)),
          ((galFC₁ j σ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ t) (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧

      (∀ j (σ : S₁), ∃ n : (ℍ[ℚ, a₂, b₂])ˣ,
        n ∈ Subgroup.normalizer ((Γ₁ j : Subgroup (ℍ[ℚ, a₂, b₂])ˣ) : Set (ℍ[ℚ, a₂, b₂])ˣ) ∧ (sgn₁ σ = 1 ↔ Even (padicValRat q' (nrd (n : ℍ[ℚ, a₂, b₂])))) ∧
        ∀ y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)),
          ((galFC₁ j σ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ (scalar₁ σ))) (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) = 1 → sgn₁ (ιS₁ τ) = 1) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) ≠ 1 → sgn₁ (ιS₁ τ) = sgn₁ σ₀₁) ∧
      sgn₁ σ₀₁ = -1 ∧ sgn₁ σ₁₁ = 1 ∧
      (∀ (α : HeckeTower.Arr q q') (σ : S₁)
        (φC : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ (HeckeTower.cod α))) →ₐ[A₁.valuation.Completion] ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ (HeckeTower.dom α)))),
        (∀ x, (φC x : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = (if α.2 = 0 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else s₁ α.1) • (x : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) →
        ∀ x, galFC₁ (HeckeTower.dom α) σ • φC x = φC (galFC₁ (HeckeTower.cod α) σ • x)) := by sorry
