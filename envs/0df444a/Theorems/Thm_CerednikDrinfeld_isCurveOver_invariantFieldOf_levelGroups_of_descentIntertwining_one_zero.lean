-- Prove2me | Theorems.Thm_CerednikDrinfeld_isCurveOver_invariantFieldOf_levelGroups_of_descentIntertwining_one_zero
-- name    : CerednikDrinfeld.isCurveOver_invariantFieldOf_levelGroups_of_descentIntertwining_one_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/9136731a-82a8-5b84-a78d-8adc444745b2
-- title:
--   Invariant fields of the level groups at q' are curves
-- statement:
--   Throughout, $\mathbb H = \mathbb H[\mathbb Q, a_2, b_2]$ denotes the rational quaternion algebra attached to $a_2, b_2 \in \mathbb Q$, $\mathrm{nrd}(x) = x_{\mathrm{re}}^2 - a_2 x_{\mathrm{imI}}^2 - b_2 x_{\mathrm{imJ}}^2 + a_2b_2 x_{\mathrm{imK}}^2$ is its reduced norm, $K_0 = \mathtt{ValuationSubring.ratClosure}\,A_1$ is the topological closure of the prime subfield inside the completion $C = A_1.\mathtt{valuation.Completion}$ of the valued field attached to a valuation subring $A_1$ of $\overline{\mathbb Q}$, and $\mathrm{Obj}(q,q') = \mathtt{Option}\{\ell \text{ prime} : \ell \neq q,\ \ell \neq q'\}$ indexes the storeys of the Hecke tower.
--
--   Numerical data: rationals $a_2, b_2$ and naturals $N, q, q'$ with $N \neq 0$, $N$ squarefree, $q$ and $q'$ prime, $q \nmid N$, $q' \nmid N$, $q' \neq q$, $q \geq 5$ and $q' \geq 5$.
--
--   Quaternionic data. The hypothesis `hdef₂` says $a_2 < 0$, $b_2 < 0$, and that for a finite place $v$ of $\mathbb Q$ every nonzero element of $\mathbb H \otimes_{\mathbb Q} \mathbb Q_v$ is a unit exactly when $q \in v$; thus $\mathbb H$ is definite and ramified at precisely the place $q$. Further, $\Lambda_2$ and $R_2$ are $\mathbb Z$-submodules of $\mathbb H$ with $\Lambda_2$ a maximal order (an order: containing $1$, multiplicatively closed, $\mathbb Q$-spanning and finitely generated; maximal among orders containing it), $R_2$ an Eichler order of level $N$ (an intersection $\Lambda_1' \cap \Lambda_2'$ of two maximal orders whose relative index in $\Lambda_1'$ is $N$), and $R_2 \leq \Lambda_2$. An element $n_2$ of the group of units of $\mathbb H \otimes_{\mathbb Q} \mathbb A_{\mathbb Q,\mathrm{fin}}$ is given, lying in $\mathtt{primeHeckeSet}\,R_2\,q'$, that is: $n_2$ lies in the finite-adelic box of $R_2$, $q' \cdot n_2^{-1}$ lies in that box, while $n_2^{-1}$ and $q'^{-1} n_2$ do not. Writing $\mathtt{meetOrder}\,R_2\,n_2 = R_2 \cap n_2 R_2 n_2^{-1}$ (intersection with the conjugate of the adelic box of $R_2$ by $n_2$, pulled back to $\mathbb H$), the hypotheses require: `hS₂`, that $\mathtt{meetOrder}\,R_2\,n_2$ is an Eichler order of level $Nq'$; `hnorm₂`, that conjugation by $n_2$ fixes it; and `hsq₂`, that the shift $x \mapsto [\,x_{\mathrm{out}} n_2\,]$ on the class set of the finite-idele stabiliser of $\mathtt{meetOrder}\,R_2\,n_2$ is an involution. The two class sets involved are assumed finite.
--
--   Hecke laws. The hypothesis `hlaws₂` is $\mathtt{ClassSetHeckeLaws}\,N\,q'\,\Lambda_2\,R_2\,n_2$: the edge Hecke matrices on the class set of the stabiliser of $\mathtt{meetOrder}\,R_2\,n_2$ commute pairwise; the vertex Hecke matrices on the class set of the stabiliser of $R_2$ commute pairwise; for every prime $\ell \neq q'$ and each $i \in \{0,1\}$ the $i$-th degeneracy pushforward intertwines the edge operator at $\ell$ with the vertex operator at $\ell$; and every edge operator preserves the common kernel of the two degeneracy pushforwards.
--
--   The place above $q'$. A valuation subring $A_1$ of $\overline{\mathbb Q}$ is given with $q'$ in its set of nonunits, its decomposition subgroup over $\mathbb Q$ acts by isometries for $A_1.\mathtt{valuation}$, and $v_1$ is a height-one prime of $\mathcal O_{\mathbb Q}$ containing $q'$.
--
--   The Hecke tower over $\overline{\mathbb Q}$. A field $F_N$ is given which is a $\overline{\mathbb Q}$-algebra, is a curve over $\overline{\mathbb Q}$ in the sense of `IsCurveOver` (principal divisors exist, every place has residue field finite over the base, and the module of Kähler differentials is free of rank one) and is essentially of finite type over $\overline{\mathbb Q}$; $\mathbb T$ is a $\mathtt{HeckeTower.TowerData}\,q\,q'\,F_N$, i.e. a family of fields $\mathbb T.F(\ell)$ indexed by the primes $\ell \neq q,q'$, each a curve over $\overline{\mathbb Q}$ and essentially of finite type, together with $\overline{\mathbb Q}$-algebra maps $F_N \to \mathbb T.F(\alpha_1)$ for each arrow $\alpha$, finite and integral along each arrow. The hypothesis `hfg` requires, for every storey $j$, an element $x$ of $\mathbb T.\mathtt{objField}\,j$ (equal to $F_N$ for $j = \mathtt{none}$ and to $\mathbb T.F(\ell)$ for $j = \mathtt{some}\,\ell$) transcendental over $\overline{\mathbb Q}$ with $\mathbb T.\mathtt{objField}\,j$ finite over $\overline{\mathbb Q}(x)$.
--
--   Semilinear data. Homomorphisms $\mathtt{galN}$ and $\mathtt{galT}(\ell)$ from the decomposition subgroup of $A_1$ over $\mathbb Q$ into the groups of semilinear automorphisms of $F_N$ and of $\mathbb T.F(\ell)$ over $\overline{\mathbb Q}$ (pairs consisting of a ring automorphism of the field and one of the base, compatible with the structure map) are given, and `hgalN`, `hgalT` say that the base component of the image of $\tau$ is $\tau$ itself. Moreover $W$ is a pair of semilinear automorphisms of $F_N$ and $WT(\ell)$ a pair for each $\mathbb T.F(\ell)$.
--
--   Mumford-side parameters. An injective $\mathbb Q$-algebra map $\iota_1 : \mathbb H \to M_2(K_0)$ is given, together with $\rho_1 : \mathbb H^\times \to \mathrm{PGL}_2(K_0)$ satisfying $\rho_1(x) = [\iota_1(x)]$; a pseudo-uniformizer $\varpi_1$ of $K_0$ in $C$ (an element whose image has valuation strictly between $0$ and $1$, with the scaling property of `PseudoUniformizer`) whose image in $C$ is $q'$; and the holomorphic ring $\mathtt{HolRingOf}\,\varpi_1\,\rho_1$ — functions on the upper half plane over $K_0 \subseteq C$ that are holomorphic on every affinoid of the $\varpi_1$-exhaustion — is assumed to be a domain.
--
--   Storey elements and level groups. Elements $s_1(\ell) \in \mathbb H^\times$ and $sf_1(\ell)$ in the finite-adelic unit group are given, and `hs₁` requires for each prime $\ell \neq q,q'$ four conditions: at every place $u$ not containing $q'$ the local component of $sf_1(\ell)$ equals $s_1(\ell) \otimes 1$; at every place containing $q'$ it equals $1$; the product of the diagonal idele of $\ell$ with $sf_1(\ell)^{-1}$ lies in $\mathtt{levelHeckeUSet}\,\Lambda_2\,(\mathtt{meetOrder}\,R_2\,n_2)\,\ell$ when $\ell \mid N$ and in $\mathtt{primeHeckeSet}\,(\mathtt{meetOrder}\,R_2\,n_2)\,\ell$ otherwise; and $\mathrm{nrd}(s_1(\ell)) = \ell$. The level groups $\Gamma_1 : \mathrm{Obj}(q,q') \to$ subgroups of $\mathbb H^\times$ satisfy: `hΓ₁0`, $\Gamma_1(\mathtt{none})$ consists of the units lying in $\mathtt{awayUnits}\,R_2\,v_1$ (units whose image at each place $w \neq v_1$ belongs to the subgroup generated by the local box units of $R_2$ at $w$) whose reduced norm has even $q'$-adic valuation; and `hΓ₁ℓ`, $\Gamma_1(\mathtt{some}\,\ell) = \Gamma_1(\mathtt{none}) \cap s_1(\ell)\,\Gamma_1(\mathtt{none})\,s_1(\ell)^{-1}$.
--
--   Distinguished elements. Maps $w_1, \bar w_1 : \mathrm{Obj}(q,q') \to \mathbb H^\times$ are given with `hw₁`: $w_1(\mathtt{none})$ lies in $\mathtt{awayUnits}\,R_2\,v_1$ and has reduced norm $q'$, and for each $\ell$, $w_1(\mathtt{some}\,\ell)$ lies in $\mathtt{awayUnits}\,(\mathtt{meetOrder}\,R_2\,(sf_1\ell))\,v_1$ and has reduced norm $q'$. The hypothesis `hwbar₁` requires for $j = \mathtt{none}$, with the order $R_2$, and for $j = \mathtt{some}\,\ell$, with the order $\mathtt{meetOrder}\,R_2\,(sf_1\ell)$: that $\mathrm{nrd}(\bar w_1(j)) = q$; that at every place $u \neq v_1$ not containing $q$ the local image of $\bar w_1(j)$ is a local box unit of that order; and that at every place $u \neq v_1$ conjugation $x \mapsto \bar w_1(j)^{-1} x\, \bar w_1(j)$ preserves membership in the local box of that order and in the local box of $\Lambda_2$.
--
--   Galois action on the completion and the descent datum. A homomorphism $\mathtt{dIso}_1$ from the decomposition subgroup into the isometric automorphisms of $C$ over $K_0$ is given, realising the natural action, $\tau \mapsto (x \mapsto \tau \cdot x)$; a character $\chi_1$ from the decomposition subgroup to $\mathbb Z/2$; and ring maps $\iota M_1(j) : \mathbb T.\mathtt{objField}\,j \to \mathrm{Frac}(\mathtt{HolRingOf}\,\varpi_1\,\rho_1)$. The final hypothesis `hI` is the predicate $\mathtt{DescentIntertwining}$ applied to $r = q'$, the index pair $(1,0)$, and all of the data $A_1, \rho_1, \varpi_1, \Gamma_1, w_1, \bar w_1, s_1, \mathtt{dIso}_1, F_N, \mathbb T, \mathtt{galN}, \mathtt{galT}, W, WT, \chi_1, \iota M_1$. Among its clauses: $\chi_1$ is trivial on the inertia subgroup; $\chi_1(\varphi) \neq 1$ for every $\varphi$ that is a Frobenius at $q'$ for $A_1$; $\chi_1(\tau) = 1$ holds exactly when $\tau$ fixes every element $x$ of the residue field of $A_1$ with $x^{q'^2} = x$; each $\iota M_1(j)$ carries a scalar $z \in \overline{\mathbb Q}$ to the image of $z$ under $C \to \mathrm{Frac}(\mathtt{HolRingOf}\,\varpi_1\,\rho_1)$; and the remaining clauses couple the tower $\mathbb T$, its semilinear Galois actions and the automorphisms $W, WT$ with the Mumford-side data through the maps $\iota M_1(j)$.
--
--   Conclusion. For every storey $j \in \mathrm{Obj}(q,q')$, write $\mathfrak M(\Gamma_1 j) = \mathtt{Mumford.invariantFieldOf}\,C\,\mathbb H^\times\,(\mathtt{HolRingOf}\,\varpi_1\,\rho_1)\,(\Gamma_1 j)$ for the subfield of $\mathrm{Frac}(\mathtt{HolRingOf}\,\varpi_1\,\rho_1)$ of elements fixed by every element of $\Gamma_1 j$. Then three assertions hold: first, $\mathfrak M(\Gamma_1 j)$ is a curve over $C$ in the sense of `IsCurveOver`, i.e. it has principal divisors over $C$, every place of $\mathfrak M(\Gamma_1 j)$ over $C$ has residue field finite over $C$, and the module of Kähler differentials of $\mathfrak M(\Gamma_1 j)$ over $C$ is free of rank one; second, $\mathfrak M(\Gamma_1 j)$ is essentially of finite type over $C$; third, there exists $x \in \mathfrak M(\Gamma_1 j)$ transcendental over $C$ such that $\mathfrak M(\Gamma_1 j)$ is finite-dimensional over the intermediate field $C(x)$ generated by $x$.
--
--   This is the statement that, in the Čerednik–Drinfeld frame at the place of $\overline{\mathbb Q}$ above $q'$, the Mumford quotient fields attached to all the level groups $\Gamma_1 j$ of the Hecke tower are one-variable function fields over the completion $C$, presented with no tree, no discrete valuation ring and no type-preserving subgroup in the statement. It supplies the curve input for the construction of Shimura-curve models with good reduction and the accompanying equivariant uniformisation, in [`CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_isCurveOver_invariantFieldOf_levelGroups_of_descentIntertwining_one_zero.lean

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

theorem CerednikDrinfeld.isCurveOver_invariantFieldOf_levelGroups_of_descentIntertwining_one_zero

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
    ∀ j : HeckeTower.Obj q q',
      IsCurveOver A₁.valuation.Completion ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)) ∧
      Algebra.EssFiniteType A₁.valuation.Completion ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)) ∧
      ∃ x : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)),
        Transcendental A₁.valuation.Completion x ∧
        FiniteDimensional ↥(IntermediateField.adjoin A₁.valuation.Completion ({x} : Set ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))))
          ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)) := by sorry
