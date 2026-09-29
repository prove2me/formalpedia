-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_cartierAnchors_degeneracyDuality_jZero_ssPlaces_correspondence_arithFrobC_restrictAlong_placeWidthChar
-- name    : CerednikDrinfeld.exists_cartierAnchors_degeneracyDuality_jZero_ssPlaces_correspondence_arithFrobC_restrictAlong_placeWidthChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/204c3767-9ca0-52cb-9c9c-27d523c9a582
-- title:
--   Cartier anchors for toric monodromy, with witnesses identified
-- statement:
--   Fix natural numbers $M, s, q'$, all nonzero, with $s$ and $q'$ prime, $s \neq q'$, and neither $q'$ nor $s$ dividing $M$.
--
--   Two groups of level hypotheses are imposed. At level $(Mq')s$: `hin₁ : HeckeInputsAll ((M * q') * s)` asserts that for every prime $\ell$ the data `HeckeInputsAlong` over $\overline{\mathbb{Q}}$ are available at level $(Mq')s$ and $\ell$ (integrality of the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar`, existence of principal divisors on the level $(Mq')s\ell$ base-changed function field, finiteness along `heckeAlphaBar`, the fundamental identity along `heckeBetaBar` and the norm formula along `heckeAlphaBar`), and `hcomm₁ : HeckeOperatorsCommuteBar ((M * q') * s)` asserts that the operators `heckeOperatorBar` at that level commute pairwise. The hypotheses `hin₂`, `hcomm₂` are the same statements at level $Mq'$. Through `heckeModuleBar` these make $J^0((Mq')s)$ and $J^0(Mq')$ modules over $\mathbb{T} =$ `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$, where $J^0(N) =$ `JZero N` is the degree-zero divisor class group $\mathrm{Pic}^0$ of the level-$N$ full modular function field base-changed to $\overline{\mathbb{Q}}$, and $X_\ell =$ `heckeGen ℓ` acts by the $\ell$-th Hecke operator.
--
--   Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime q'`, i.e. $q'$ lies in the nonunits of $A$; consequently the residue field $\kappa =$ `IsLocalRing.ResidueField A` has characteristic $q'$. Write $\Sigma(N) =$ `ssPlaces q' N κ` for the set of supersingular places of the level-$N$ modular function field $F_N = \kappa(j(\mathsf q), j(\mathsf q^N))$ over $\kappa$, namely the places $w$ that are rational, affine geometric, and have $w$-value of the generator $j$ lying in the supersingular $j$-set `ssJSet q' κ`; the sets $\Sigma(Ms)$ and $\Sigma(M)$ are assumed finite with decidable equality. Write $\mathcal{T}(N) =$ `toricMonodromyPart q' (A.inertiaSubgroupIn ℚ)` inside $J^0(N)$: the $\mathbb{T}$-submodule spanned by the elements $\sigma \cdot x - x$ with $\sigma$ in the image of the inertia subgroup of $A$ over $\mathbb{Q}$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and $x$ annihilated by some positive integer coprime to $q'$. Write $L(\Sigma) =$ `characterLattice Σ` for the kernel of the sum-of-coordinates map on $\Sigma \to \mathbb{Z}$.
--
--   The conclusion asserts the existence of the following data. Families of integer matrices $T_1(\ell)$ indexed by $\Sigma(Ms) \times \Sigma(Ms)$ and $T_2(\ell)$ indexed by $\Sigma(M) \times \Sigma(M)$, one for each prime $\ell$; integers $n_1(\ell)$, $n_2(\ell)$; witnesses `hcol₁`, `hcol₂` that for every $\ell$ all row sums of $T_1(\ell)^{\mathsf T}$ equal $n_1(\ell)$ and all row sums of $T_2(\ell)^{\mathsf T}$ equal $n_2(\ell)$, i.e. every column sum of $T_i(\ell)$ is $n_i(\ell)$; isomorphisms of additive groups
--   $$\varepsilon_1 : \mathcal{T}((Mq')s) \xrightarrow{\ \sim\ } \operatorname{Hom}\bigl(L(\Sigma(Ms)), \mathrm{Additive}\,\kappa^\times\bigr), \qquad \varepsilon_2 : \mathcal{T}(Mq') \xrightarrow{\ \sim\ } \operatorname{Hom}\bigl(L(\Sigma(M)), \mathrm{Additive}\,\kappa^\times\bigr);$$
--   a pair of maps $ab : \mathrm{Fin}\,2 \to (\Sigma(Ms) \to \Sigma(M))$; weights $w : \Sigma(Ms) \to \mathbb{Z}_{>0}$ and $w_V : \Sigma(M) \to \mathbb{Z}_{>0}$; a pair of $\mathbb{Z}$-linear maps $\mathrm{padj}\,i : (\Sigma(M) \to \mathbb{Z}) \to (\Sigma(Ms) \to \mathbb{Z})$; a witness `hres` that for each $i \in \mathrm{Fin}\,2$ the degeneracy pushforward `degeneracyPushforwardPair (M * q') s i` $: J^0((Mq')s) \to J^0(Mq')$ carries $\mathcal{T}((Mq')s)$ into $\mathcal{T}(Mq')$; and a witness `hlat` that each $\mathrm{padj}\,i$ carries $L(\Sigma(M))$ into $L(\Sigma(Ms))$. Throughout, `degeneracyMatrix (ab i)` is the incidence matrix with $(v,e)$ entry $1$ if $ab\,i\,(e) = v$ and $0$ otherwise.
--
--   These data satisfy the following twenty-three assertions.
--
--   (1) For every prime $\ell$, every $y \in \mathcal{T}((Mq')s)$ and every $x \in L(\Sigma(Ms))$, $\varepsilon_1(X_\ell \cdot y)(x) = \varepsilon_1(y)\bigl(\mathrm{heckeCharacterAction}\,(T_1(\ell)^{\mathsf T})\,x\bigr)$, where the latter operator sends $x$ to $T_1(\ell)x$.
--
--   (2) The same identity for $\varepsilon_2$, $T_2(\ell)$ and $L(\Sigma(M))$.
--
--   (3) $T_1(\ell)$ and $T_1(\ell')$ commute for all primes $\ell, \ell'$.
--
--   (4) $T_2(\ell)$ and $T_2(\ell')$ commute for all primes $\ell, \ell'$.
--
--   (5) For each $i \in \mathrm{Fin}\,2$ and each prime $\ell \neq s$, $\;\mathrm{deg}(ab\,i) \cdot T_1(\ell) = T_2(\ell) \cdot \mathrm{deg}(ab\,i)$, where $\mathrm{deg}(ab\,i) =$ `degeneracyMatrix (ab i)`.
--
--   (6) If $x : \Sigma(Ms) \to \mathbb{Z}$ satisfies $\mathrm{deg}(ab\,i)\,x = 0$ for both $i$, then $\mathrm{deg}(ab\,i)\,(T_1(s)x) = 0$ for both $i$.
--
--   (7) For every prime $\ell$ not dividing $(Mq')s$ and all indices $i, j$: $w(i)\,T_1(\ell)_{ij} = w(j)\,T_1(\ell)_{ji}$.
--
--   (8) For every prime $\ell$ not dividing $Mq'$ and all indices $i, j$: $w_V(i)\,T_2(\ell)_{ij} = w_V(j)\,T_2(\ell)_{ji}$.
--
--   (9) $n_1(\ell) = \ell + 1$ for every prime $\ell \nmid (Mq')s$.
--
--   (10) $n_2(\ell) = \ell + 1$ for every prime $\ell \nmid Mq'$.
--
--   (11) There is a permutation $\sigma$ of $\Sigma(Ms)$ with $T_1(q')_{ij} = 1$ if $i = \sigma(j)$ and $0$ otherwise.
--
--   (12) There is a permutation $\sigma$ of $\Sigma(M)$ with $T_2(q')_{ij} = 1$ if $i = \sigma(j)$ and $0$ otherwise.
--
--   (13) For each $i$, each $x : \Sigma(M) \to \mathbb{Z}$ and each $y : \Sigma(Ms) \to \mathbb{Z}$,
--   $$\sum_{v \in \Sigma(M)} w_V(v)\,\bigl(\mathrm{deg}(ab\,i)\,y\bigr)(v)\,x(v) = \sum_{e \in \Sigma(Ms)} w(e)\,y(e)\,(\mathrm{padj}\,i\,x)(e),$$
--   so $\mathrm{padj}\,i$ is adjoint to $\mathrm{deg}(ab\,i)$ for the weighted pairings.
--
--   (14) For each $i$, each $y \in \mathcal{T}((Mq')s)$ and each $x \in L(\Sigma(M))$, $\varepsilon_2\bigl(\mathrm{degeneracyPushforwardPair}\,(Mq')\,s\,i\,y\bigr)(x) = \varepsilon_1(y)(\mathrm{padj}\,i\,x)$, the memberships being supplied by `hres` and `hlat`.
--
--   (15) For every prime $\ell \neq q'$, assuming the existence of principal divisors on the roof field `charLDegeneracyRoof κ (M * s) ℓ` and integrality hypotheses $h_{\alpha c} :$ `HeckeAlphaCIntegral κ (M * s) ℓ`, $h_{\beta c} :$ `HeckeBetaCIntegral κ (M * s) ℓ`, one has for all $y, x \in \Sigma(Ms)$ that $T_1(\ell)_{yx}$ is the coefficient at $y$ of the divisor correspondence [`AlgebraicCurve.Divisor.correspondence`](def/AlgebraicCurve_Correspondence.html#L137) attached to `heckeAlphaC` and `heckeBetaC` (pullback along the inclusion $\alpha$ followed by pushforward along the $\mathsf q \mapsto \mathsf q^\ell$ map $\beta$) applied to the divisor $1 \cdot x$.
--
--   (16) The same description of $T_2(\ell)_{yx}$ at level $M$, for $y, x \in \Sigma(M)$.
--
--   (17) For all $y, x \in \Sigma(Ms)$: $T_1(q')_{yx} = 1$ if and only if `arithFrobC q' κ (M * s)`, the semilinear automorphism of $F_{Ms}$ given by the Frobenius of $\kappa$ on coefficients, carries the place $y$ to the place $x$.
--
--   (18) The same criterion for $T_2(q')$ and `arithFrobC q' κ M` on $\Sigma(M)$.
--
--   (19) For every $x \in \Sigma(Ms)$, applying `arithFrobC q' κ (M * s)` twice to $x$ returns $x$.
--
--   (20) For every $x \in \Sigma(M)$, applying `arithFrobC q' κ M` twice to $x$ returns $x$.
--
--   (21) For any pair $\varphi : \mathrm{Fin}\,2 \to (F_M \to_{\mathrm{alg}[\kappa]} F_{Ms})$ of $\kappa$-algebra maps with integral underlying ring maps, such that $\varphi\,0$ is the identity on Laurent series and $\varphi\,1$ is the operator `qExpand κ s`, and for every $i$ and every $p \in \Sigma(Ms)$: the restriction of the place $p$ along $\varphi\,i$, [`AlgebraicCurve.Place.restrictAlong`](def/AlgebraicCurve_Correspondence.html#L204), equals $ab\,i\,(p)$.
--
--   (22) For every $p \in \Sigma(Ms)$: $w(p) =$ `placeWidthChar q' (M * s) p`, the characteristic-adjusted $j$-width at $p$ divided by the $j$-ramification of $p$.
--
--   (23) For every $v \in \Sigma(M)$: $w_V(v) =$ `placeWidthChar q' M v`.
--
--   This is the Čerednik–Drinfeld/Ribet description of the toric monodromy part at $q'$ of the Jacobians $J_0(Mq's)$ and $J_0(Mq')$ as the character group of a torus indexed by supersingular points in characteristic $q'$, in the form of an anchored package: Hecke action by explicit integer matrices on supersingular places, with the matrices at $q'$ identified with arithmetic Frobenius, the matrices away from $q'$ with the $\beta_*\alpha^*$ divisor correspondence, the degeneracy maps with restriction of places, and the weights with place widths. It is cited by [`ModularCurve.exists_cartierAnchor_toricMonodromyPart_ssHeckeFamilyC`](thm.html#ModularCurve.exists_cartierAnchor_toricMonodromyPart_ssHeckeFamilyC), feeding the level-lowering step of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_cartierAnchors_degeneracyDuality_jZero_ssPlaces_correspondence_arithFrobC_restrictAlong_placeWidthChar.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_CerednikDrinfeld_Ribbon
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open ModularCurve

theorem CerednikDrinfeld.exists_cartierAnchors_degeneracyDuality_jZero_ssPlaces_correspondence_arithFrobC_restrictAlong_placeWidthChar
    (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero q'] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (hin₁ : HeckeInputsAll ((M * q') * s)) (hcomm₁ : HeckeOperatorsCommuteBar ((M * q') * s))
    (hin₂ : HeckeInputsAll (M * q')) (hcomm₂ : HeckeOperatorsCommuteBar (M * q'))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q')
    [DecidableEq (IsLocalRing.ResidueField A)]
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField A))]
    [DecidableEq ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField A))] :
    letI := heckeModuleBar ((M * q') * s)
    letI := heckeModuleBar (M * q')
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (IsLocalRing.ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    ∃ (T₁ : Nat.Primes → Matrix (↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)))
          (↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))) ℤ)
      (n₁ : Nat.Primes → ℤ)
      (hcol₁ : ∀ ℓ : Nat.Primes, HeckeRowSums (T₁ ℓ).transpose (n₁ ℓ))
      (ε₁ : ↥(toricMonodromyPart (J := JZero ((M * q') * s)) q' (A.inertiaSubgroupIn ℚ)) ≃+
          (↥(characterLattice ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))) →+
            Additive (IsLocalRing.ResidueField A)ˣ))
      (T₂ : Nat.Primes → Matrix (↥(ssPlaces q' M (IsLocalRing.ResidueField A)))
          (↥(ssPlaces q' M (IsLocalRing.ResidueField A))) ℤ)
      (n₂ : Nat.Primes → ℤ)
      (hcol₂ : ∀ ℓ : Nat.Primes, HeckeRowSums (T₂ ℓ).transpose (n₂ ℓ))
      (ε₂ : ↥(toricMonodromyPart (J := JZero (M * q')) q' (A.inertiaSubgroupIn ℚ)) ≃+
          (↥(characterLattice ↥(ssPlaces q' M (IsLocalRing.ResidueField A))) →+
            Additive (IsLocalRing.ResidueField A)ˣ))
      (ab : Fin 2 → (↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)) →
          ↥(ssPlaces q' M (IsLocalRing.ResidueField A))))
      (w : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)) → ℕ+)
      (wV : ↥(ssPlaces q' M (IsLocalRing.ResidueField A)) → ℕ+)
      (padj : Fin 2 → ((↥(ssPlaces q' M (IsLocalRing.ResidueField A)) → ℤ) →ₗ[ℤ]
          (↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)) → ℤ)))
      (hres : ∀ (i : Fin 2) (y : JZero ((M * q') * s)),
          y ∈ toricMonodromyPart (J := JZero ((M * q') * s)) q' (A.inertiaSubgroupIn ℚ) →
          (degeneracyPushforwardPair (M * q') s i) y ∈
            toricMonodromyPart (J := JZero (M * q')) q' (A.inertiaSubgroupIn ℚ))
      (hlat : ∀ (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField A)) → ℤ),
          x ∈ characterLattice ↥(ssPlaces q' M (IsLocalRing.ResidueField A)) →
          padj i x ∈ characterLattice ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))),
      (∀ (ℓ : Nat.Primes)
          (y : ↥(toricMonodromyPart (J := JZero ((M * q') * s)) q' (A.inertiaSubgroupIn ℚ)))
          (x : ↥(characterLattice ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)))),
          ε₁ (heckeGen ℓ • y) x = ε₁ y (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x)) ∧
      (∀ (ℓ : Nat.Primes)
          (y : ↥(toricMonodromyPart (J := JZero (M * q')) q' (A.inertiaSubgroupIn ℚ)))
          (x : ↥(characterLattice ↥(ssPlaces q' M (IsLocalRing.ResidueField A)))),
          ε₂ (heckeGen ℓ • y) x = ε₂ y (heckeCharacterAction (T₂ ℓ).transpose (hcol₂ ℓ) x)) ∧
      (∀ ℓ ℓ' : Nat.Primes, Commute (T₁ ℓ) (T₁ ℓ')) ∧
      (∀ ℓ ℓ' : Nat.Primes, Commute (T₂ ℓ) (T₂ ℓ')) ∧
      (∀ (i : Fin 2) (ℓ : Nat.Primes), (ℓ : ℕ) ≠ s →
          degeneracyMatrix (ab i) * T₁ ℓ = T₂ ℓ * degeneracyMatrix (ab i)) ∧
      (∀ x : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)) → ℤ,
          (∀ i : Fin 2, (degeneracyMatrix (ab i)).mulVec x = 0) →
          ∀ i : Fin 2, (degeneracyMatrix (ab i)).mulVec ((T₁ ⟨s, hs⟩).mulVec x) = 0) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ (M * q') * s →
          ∀ i j, (w i : ℤ) * T₁ ℓ i j = (w j : ℤ) * T₁ ℓ j i) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M * q' →
          ∀ i j, (wV i : ℤ) * T₂ ℓ i j = (wV j : ℤ) * T₂ ℓ j i) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ (M * q') * s → n₁ ℓ = ((ℓ : ℕ) : ℤ) + 1) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M * q' → n₂ ℓ = ((ℓ : ℕ) : ℤ) + 1) ∧
      (∃ σ : Equiv.Perm ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)),
          ∀ i j, T₁ ⟨q', hq'⟩ i j = if i = σ j then 1 else 0) ∧
      (∃ σ : Equiv.Perm ↥(ssPlaces q' M (IsLocalRing.ResidueField A)),
          ∀ i j, T₂ ⟨q', hq'⟩ i j = if i = σ j then 1 else 0) ∧
      (∀ (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField A)) → ℤ)
          (y : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)) → ℤ),
          (∑ v, (wV v : ℤ) * (degeneracyMatrix (ab i)).mulVec y v * x v) =
            ∑ e, (w e : ℤ) * y e * padj i x e) ∧
      (∀ (i : Fin 2)
          (y : ↥(toricMonodromyPart (J := JZero ((M * q') * s)) q' (A.inertiaSubgroupIn ℚ)))
          (x : ↥(characterLattice ↥(ssPlaces q' M (IsLocalRing.ResidueField A)))),
          ε₂ ⟨(degeneracyPushforwardPair (M * q') s i) ↑y, hres i ↑y y.2⟩ x =
            ε₁ y ⟨padj i ↑x, hlat i ↑x x.2⟩) ∧
      (∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q' →
          (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
            ∀ [AlgebraicCurve.HasPrincipalDivisors (IsLocalRing.ResidueField A)
                (ModularCurve.charLDegeneracyRoof (IsLocalRing.ResidueField A) (M * s) ℓ)]
              (hαc : ModularCurve.HeckeAlphaCIntegral (IsLocalRing.ResidueField A) (M * s) ℓ)
              (hβc : ModularCurve.HeckeBetaCIntegral (IsLocalRing.ResidueField A) (M * s) ℓ)
              (y x : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))),
              T₁ ℓ y x = AlgebraicCurve.Divisor.correspondence
                (ModularCurve.heckeAlphaC (IsLocalRing.ResidueField A) (M * s) ℓ)
                (ModularCurve.heckeBetaC (IsLocalRing.ResidueField A) (M * s) ℓ) hαc hβc
                (Finsupp.single x.1 1) y.1)) ∧
      (∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q' →
          (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
            ∀ [AlgebraicCurve.HasPrincipalDivisors (IsLocalRing.ResidueField A)
                (ModularCurve.charLDegeneracyRoof (IsLocalRing.ResidueField A) M ℓ)]
              (hαc : ModularCurve.HeckeAlphaCIntegral (IsLocalRing.ResidueField A) M ℓ)
              (hβc : ModularCurve.HeckeBetaCIntegral (IsLocalRing.ResidueField A) M ℓ)
              (y x : ↥(ssPlaces q' M (IsLocalRing.ResidueField A))),
              T₂ ℓ y x = AlgebraicCurve.Divisor.correspondence
                (ModularCurve.heckeAlphaC (IsLocalRing.ResidueField A) M ℓ)
                (ModularCurve.heckeBetaC (IsLocalRing.ResidueField A) M ℓ) hαc hβc
                (Finsupp.single x.1 1) y.1)) ∧
      (∀ y x : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)),
          T₁ ⟨q', hq'⟩ y x = 1 ↔
            arithFrobC q' (IsLocalRing.ResidueField A) (M * s) • (y.1 : AlgebraicCurve.Place (IsLocalRing.ResidueField A) (modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))) = x.1) ∧
      (∀ y x : ↥(ssPlaces q' M (IsLocalRing.ResidueField A)),
          T₂ ⟨q', hq'⟩ y x = 1 ↔
            arithFrobC q' (IsLocalRing.ResidueField A) M • (y.1 : AlgebraicCurve.Place (IsLocalRing.ResidueField A) (modularFunctionFieldC (IsLocalRing.ResidueField A) M)) = x.1) ∧
      (∀ x : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)),
          arithFrobC q' (IsLocalRing.ResidueField A) (M * s) • (arithFrobC q' (IsLocalRing.ResidueField A) (M * s) •
            (x.1 : AlgebraicCurve.Place (IsLocalRing.ResidueField A) (modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s)))) = x.1) ∧
      (∀ x : ↥(ssPlaces q' M (IsLocalRing.ResidueField A)),
          arithFrobC q' (IsLocalRing.ResidueField A) M • (arithFrobC q' (IsLocalRing.ResidueField A) M •
            (x.1 : AlgebraicCurve.Place (IsLocalRing.ResidueField A) (modularFunctionFieldC (IsLocalRing.ResidueField A) M))) = x.1) ∧
      (∀ (φ : Fin 2 → (↥(modularFunctionFieldC (IsLocalRing.ResidueField A) M) →ₐ[IsLocalRing.ResidueField A]
              ↥(modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))))
          (hφ : ∀ i, (φ i).toRingHom.IsIntegral),
          (∀ x, ((φ 0 x : ↥(modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))) :
              LaurentSeries (IsLocalRing.ResidueField A)) = x) →
          (∀ x, ((φ 1 x : ↥(modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))) :
              LaurentSeries (IsLocalRing.ResidueField A)) = qExpand (IsLocalRing.ResidueField A) s x) →
          ∀ (i : Fin 2) (p : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))),
            AlgebraicCurve.Place.restrictAlong (φ i) (hφ i) (↑p) = ↑(ab i p)) ∧
      (∀ p : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)), (w p : ℕ) = placeWidthChar q' (M * s) p.1) ∧
      (∀ v : ↥(ssPlaces q' M (IsLocalRing.ResidueField A)), (wV v : ℕ) = placeWidthChar q' M v.1) := by sorry
