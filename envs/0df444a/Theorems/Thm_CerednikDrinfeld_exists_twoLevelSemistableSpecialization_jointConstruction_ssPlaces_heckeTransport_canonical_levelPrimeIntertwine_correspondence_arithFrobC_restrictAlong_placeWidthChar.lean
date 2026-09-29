-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_twoLevelSemistableSpecialization_jointConstruction_ssPlaces_heckeTransport_canonical_levelPrimeIntertwine_correspondence_arithFrobC_restrictAlong_placeWidthChar
-- name    : CerednikDrinfeld.exists_twoLevelSemistableSpecialization_jointConstruction_ssPlaces_heckeTransport_canonical_levelPrimeIntertwine_correspondence_arithFrobC_restrictAlong_placeWidthChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/d421a9b7-92cc-56ac-a17e-e621406508d7
-- title:
--   Two-level joint semistable specialisation with pinned Hecke transport
-- statement:
--   Throughout, $\kappa$ denotes the residue field `IsLocalRing.ResidueField A` of the valuation subring $A$, for a level $N$ the field $F_N$ is `modularFunctionFieldC κ N` (the subfield of `LaurentSeries κ` generated over $\kappa$ by `jqModC κ` and `jqNModC κ N`), and `JZero N` is `Pic0` of the base-changed modular function field `modularFunctionFieldBar N` over an algebraic closure of $\mathbb{Q}$.
--
--   Data and hypotheses. Let $M$, $s$, $q'$ be non-zero natural numbers with $s$ and $q'$ prime (`hs`, `hq'`), $s \neq q'$ (`hsq'`), $q' \nmid M$ (`hq'M`) and $s \nmid M$ (`hsM`). Let $A$ be a valuation subring of `AlgebraicClosure ℚ` with `hA : A.LiesOverPrime q'`, i.e. the image of $q'$ lies in `A.nonunits`; consequently $\kappa$ has characteristic $q'$. The sets `ssPlaces q' (M * s) κ` and `ssPlaces q' M κ` of places of $F_{M\cdot s}$, resp. $F_M$, satisfying the predicate `IsSupersingularPlace` are assumed finite. The Hecke algebra `HeckeAlg` $=$ `MvPolynomial Nat.Primes ℤ` acts on `JZero` at the levels $(M s) q'$, $M s$, $M q'$ and $M$ through [`ModularCurve.heckeModuleBar`](def/ModularCurve_HeckeModule.html#L82), and `heckeGen ℓ` denotes the variable $X_\ell$.
--
--   Conclusion. There exist: two `HeckeAlg`-module structures, one on [`AlgebraicCurve.Pic0 κ F_{M·s}`](def/AlgebraicCurve_DivisorClassGroup.html#L223) and one on [`AlgebraicCurve.Pic0 κ F_M`](def/AlgebraicCurve_DivisorClassGroup.html#L223) (asserted to exist, with no further condition imposed on them); semistable specialisation data $D_1 :$ `JZeroSemistableSpecialization A (M * s) q' hq'` and $D_2 :$ `JZeroSemistableSpecialization A M q' hq'`, each consisting in particular of a finset `nodes` of pairs of places of the relevant $F_N$, a semilinear automorphism `frob` stabilising `nodes`, a width function `width`, a homomorphism `comp` from the inertia invariants into the component group `componentGroup width`, a specialisation `sp` into the glued Picard group, and the reduction `spN` from `JZero N` to `Pic0 κ F_N`; a pair $ab : \mathrm{Fin}\,2 \to (\mathrm{ssPlaces}\,q'\,(M*s)\,\kappa \to \mathrm{ssPlaces}\,q'\,M\,\kappa)$ of maps of supersingular place sets; bijections $e_1$ from `ssPlaces q' (M * s) κ` to $D_1.\mathrm{nodes}$ and $e_2$ from `ssPlaces q' M κ` to $D_2.\mathrm{nodes}$; positive widths $w$ on `ssPlaces q' (M * s) κ` and $wV$ on `ssPlaces q' M κ`; multiplicities $m : \mathrm{Fin}\,2 \to \mathrm{ssPlaces}\,q'\,(M*s)\,\kappa \to \mathbb{N}$; a pair $dpair$ of additive maps `JZero ((M * s) * q')` $\to$ `JZero (M * q')`; a pair $\Phi$ of additive maps from [`AlgebraicCurve.GluedPic0 κ F_{M·s} D₁.nodes`](def/AlgebraicCurve_GluedPic0.html#L201) to [`AlgebraicCurve.GluedPic0 κ F_M D₂.nodes`](def/AlgebraicCurve_GluedPic0.html#L201); and matrix-valued functions $T_1$ on $D_1.\mathrm{nodes}$, $T_2$ on $D_2.\mathrm{nodes}$ together with integers $n_1(\ell)$, $n_2(\ell)$, indexed by `Nat.Primes`, such that all of the following hold.
--
--   Nodes and places. $D_1.\mathrm{nodes} =$ `nodePairsOfPlaces D₁.frob` applied to the finset of supersingular places at level $M s$, that is, the image of that finset under the embedding `smulNodePairEmb D₁.frob` attached to $D_1.\mathrm{frob}$; likewise $D_2.\mathrm{nodes}$ from the supersingular places at level $M$ and $D_2.\mathrm{frob}$. For every supersingular place $p$ at level $M s$ the first component of the node pair $e_1(p)$ is $p$, and correspondingly for $e_2$ at level $M$.
--
--   Inertia differences. For every $\sigma$ in `A.inertiaSubgroupIn ℚ` (the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$) and every $x \in$ `JZero ((M * s) * q')` with `PrimeToTorsion q' x` (there is $n > 0$, $q' \nmid n$, with $n \cdot x = 0$), the element $\sigma \cdot x - x$ lies in `inertiaInvariants A ((M * s) * q')`, and for it $D_1.\mathrm{comp}$ vanishes and so does [`AlgebraicCurve.GluedPic0.toPic0Pair D₁.nodes`](def/AlgebraicCurve_GluedPic0.html#L229) applied to $D_1.\mathrm{sp}$ of it. The same statement holds at level $M q'$ with $D_2$.
--
--   Degeneracy maps and toric parts. For each $i \in \mathrm{Fin}\,2$, $dpair\,i$ carries `toricMonodromyPart q' (A.inertiaSubgroupIn ℚ)` of `JZero ((M * s) * q')` into the corresponding submodule of `JZero (M * q')`, where `toricMonodromyPart q' I` is the `HeckeAlg`-span of the elements $\sigma \cdot x - x$ with $\sigma \in I$ and $x$ killed by some positive integer coprime to $q'$. For each $i$ and each $x$ in `inertiaInvariants A ((M * s) * q')` whose image $dpair\,i\,x$ lies in `inertiaInvariants A (M * q')`, the vanishing $D_1.\mathrm{comp}\,x = 0$ implies $D_2.\mathrm{sp}(dpair\,i\,x) = \Phi_i(D_1.\mathrm{sp}\,x)$.
--
--   Numerical and glued-unit compatibilities. For all $i$ and all supersingular $p$ at level $M s$: $m\,i\,p \cdot w(p) = wV(ab\,i\,p)$. For all $i$ and all supersingular $v$ at level $M$: $\sum_{p : ab\,i\,p = v} m\,i\,p = s + 1$. For all $i$ and every $g : D_1.\mathrm{nodes} \to$ `Additive κˣ`, $\Phi_i$ sends [`AlgebraicCurve.GluedPic0.nodeUnit D₁.nodes g`](def/AlgebraicCurve_GluedPic0.html#L247) to [`AlgebraicCurve.GluedPic0.nodeUnit D₂.nodes`](def/AlgebraicCurve_GluedPic0.html#L247) of the function $n \mapsto \sum_{p_1 : ab\,i\,p_1 = e_2^{-1}(n)} m\,i\,p_1 \cdot g(e_1(p_1))$. For all $i$ and all $y \in$ `JZero ((M * s) * q')`, $z \in$ `JZero ((M * q') * s)` whose identification under the equality $(Ms)q' = (Mq')s$ matches $y$ with $z$, one has $dpair\,i\,y =$ `degeneracyPushforwardPair (M * q') s i z`, the latter being the pair of pushforwards along `heckeAlphaBar` and `heckeBetaBar` in level $M q'$ and degree $s$ when the corresponding inputs hold, and $0$ otherwise. Finally $w(p) = D_1.\mathrm{width}(e_1(p))$ for all supersingular $p$ at level $M s$, and $wV(v) = D_2.\mathrm{width}(e_2(v))$ for all supersingular $v$ at level $M$.
--
--   The specialisation dictionary for $D_1$ (nine clauses, at level $M s$ with auxiliary level $(Ms)q'$). Its first clause repeats the inertia-difference statement for $D_1$ already listed. Next: for every natural number $m$ coprime to $q'$, every $g$ in [`AlgebraicCurve.GluedPic0 κ F_{M·s} D₁.nodes`](def/AlgebraicCurve_GluedPic0.html#L201) with $m \cdot g = 0$ is of the form $D_1.\mathrm{sp}\,x$ for some $x$ in `inertiaInvariants A ((M * s) * q')` with $m \cdot x = 0$ and $D_1.\mathrm{comp}\,x = 0$; for every $m$ coprime to $q'$, every $\varphi$ in `componentGroup D₁.width` with $m \cdot \varphi = 0$ equals $D_1.\mathrm{comp}\,x$ for some such $x$ with $m \cdot x = 0$; $D_1.\mathrm{comp}$ is surjective; for every $\sigma$ in `A.decompositionSubgroup ℚ` and every $x$ in the inertia invariants whose translate $\sigma \cdot x$ again lies there, $D_1.\mathrm{comp}\,x = 0$ implies $D_1.\mathrm{comp}(\sigma \cdot x) = 0$; under the same hypotheses, if moreover `toPic0Pair D₁.nodes (D₁.sp x)` $= 0$ then the same holds for $\sigma \cdot x$; and, again under the same hypotheses, if `toPic0Pair D₁.nodes (D₁.sp x)` $= (D_1.\mathrm{spN}\,a, D_1.\mathrm{spN}\,b)$ for some $a, b \in$ `JZero (M * s)`, then `toPic0Pair D₁.nodes (D₁.sp (σ · x))` $= (D_1.\mathrm{spN}(\sigma \cdot a), D_1.\mathrm{spN}(\sigma \cdot b))$. All widths $D_1.\mathrm{width}$ are strictly positive. Lastly, there is a `HeckeAlg`-module structure on `componentGroup D₁.width` for which $D_1.\mathrm{comp}$ is Hecke-equivariant, in the sense that $D_1.\mathrm{comp}(T \cdot x) = T \cdot D_1.\mathrm{comp}\,x$ whenever $T \in$ `HeckeAlg`, $x$ and $T \cdot x$ lie in the inertia invariants, and for which the following holds: for every maximal ideal $\mathfrak{m}$ of `HeckeAlg` with `heckeTorsion (componentGroup D₁.width) 𝔪` $= \bot$, every $x$ in `heckeTorsion (JZero ((M * s) * q')) 𝔪` satisfying `PrimeToTorsion q' x`, lying in `inertiaInvariants A ((M * s) * q')`, with $D_1.\mathrm{comp}\,x = 0$ and `toPic0Pair D₁.nodes (D₁.sp x)` $= 0$, belongs to `toricMonodromyPart q' (A.inertiaSubgroupIn ℚ)` of `JZero ((M * s) * q')`. The identical list of nine clauses is asserted for $D_2$ with $M s$ replaced by $M$ and $(Ms)q'$ by $M q'$.
--
--   Hecke matrices. For every prime $\ell$ the column sums of $T_1(\ell)$ are constant: $\sum_{t} T_1(\ell)_{t,u} = n_1(\ell)$ for every node $u$ of $D_1$; and $T_1$ transports the specialisation, in that for every prime $\ell$, every $x$ in `inertiaInvariants A ((M * s) * q')` with `heckeGen ℓ` $\cdot\, x$ again in the inertia invariants and $D_1.\mathrm{comp}\,x = 0$, and every $g : D_1.\mathrm{nodes} \to$ `Additive κˣ` with $D_1.\mathrm{sp}\,x =$ `nodeUnit D₁.nodes g`, one has $D_1.\mathrm{sp}(\mathrm{heckeGen}\,\ell \cdot x) =$ `nodeUnit D₁.nodes` of the function $t \mapsto \sum_{u} T_1(\ell)_{u,t} \cdot g(u)$. The same two statements hold for $T_2$, $n_2$ and $D_2$ at level $M q'$. The matrices $T_1(\ell)$ commute pairwise, and so do the $T_2(\ell)$. For $\ell \nmid (Ms)q'$ one has $n_1(\ell) = \ell + 1$, and for $\ell \nmid M q'$ one has $n_2(\ell) = \ell + 1$. For $\ell \nmid (Ms)q'$ the width-weighted symmetry $D_1.\mathrm{width}(i)\,T_1(\ell)_{i,j} = D_1.\mathrm{width}(j)\,T_1(\ell)_{j,i}$ holds for all nodes $i, j$, and correspondingly for $T_2$ and $D_2$ when $\ell \nmid M q'$. At $\ell = q'$ the matrix is a permutation matrix: $T_1(q')_{e_1(i),e_1(j)}$ equals $1$ if $i = e_1^{-1}$ of the inverse of [`AlgebraicCurve.SemilinearAut.nodePerm D₁.nodes D₁.frob D₁.frob_nodeStable`](def/AlgebraicCurve_GluedPic0Functoriality.html#L45) applied to $e_1(j)$, and $0$ otherwise; likewise for $T_2(q')$ with $e_2$ and $D_2.\mathrm{frob}$.
--
--   Degeneracy intertwining. With `degeneracyMatrix (ab i)` the $\{0,1\}$-matrix whose $(v,p)$ entry is $1$ exactly when $ab\,i\,p = v$: for each $i$ and each prime $\ell \neq s$, `degeneracyMatrix (ab i)` $\cdot\, T_1(\ell)$ (transported to the supersingular index sets via $e_1$) equals $T_2(\ell)$ (transported via $e_2$) $\cdot\,$ `degeneracyMatrix (ab i)`. At $\ell = s$ the two relations are `degeneracyMatrix (ab 1)` $\cdot\, T_1(s) = T_2(s) \cdot$ `degeneracyMatrix (ab 1)` $-$ `degeneracyMatrix (ab 0)` and `degeneracyMatrix (ab 0)` $\cdot\, T_1(s) = s \cdot$ `degeneracyMatrix (ab 1)`, again after transport along $e_1$ and $e_2$.
--
--   Pinned identifications. For every prime $\ell \neq q'$, assuming [`AlgebraicCurve.HasPrincipalDivisors κ (charLDegeneracyRoof κ (M * s) ℓ)`](def/AlgebraicCurve_DivisorClassGroup.html#L217) and integrality of the two degeneracy embeddings (`HeckeAlphaCIntegral`, `HeckeBetaCIntegral` at level $M s$ and degree $\ell$), the entries of $T_1(\ell)$ are correspondence coefficients: for all nodes $a, b$, $T_1(\ell)_{a,b}$ is the coefficient at the first place of $a$ of [`AlgebraicCurve.Divisor.correspondence (heckeAlphaC κ (M*s) ℓ) (heckeBetaC κ (M*s) ℓ)`](def/AlgebraicCurve_Correspondence.html#L137) — pushforward along `heckeBetaC` of pullback along `heckeAlphaC` — applied to the divisor `Finsupp.single` of the first place of $b$ with coefficient $1$; the analogous statement holds for $T_2(\ell)$ at level $M$. Next, for every pair $\varphi$ of $\kappa$-algebra maps $F_M \to F_{M\cdot s}$ with integral underlying ring maps, such that $\varphi_0$ acts as the identity on Laurent series and $\varphi_1$ acts as `qExpand κ s`, and for each $i$ and each supersingular place $p$ at level $M s$, the restriction [`AlgebraicCurve.Place.restrictAlong (φ i) (hφ i) p`](def/AlgebraicCurve_Correspondence.html#L204) equals $ab\,i\,p$. The widths are the characteristic widths: $w(p) =$ `placeWidthChar q' (M * s) p` for all supersingular $p$ at level $M s$, and $wV(v) =$ `placeWidthChar q' M v` for all supersingular $v$ at level $M$, where `placeWidthChar q N w` is `jWidthChar q (w.evalAt (jGeomGen κ N))` divided by `placeRamificationJ N w`. Finally the Frobenius data are the arithmetic ones: $D_1.\mathrm{frob} =$ `arithFrobC q' κ (M * s)` and $D_2.\mathrm{frob} =$ `arithFrobC q' κ M`, the semilinear automorphisms acting on coefficients by $x \mapsto x^{q'}$.
--
--   This is the pinned form of the two-level joint semistable specialisation at the prime $q'$: it packages the character-group description of the toric part of the reduction of $J_0$ at $q'$ in levels $Ms$ and $M$, the Hecke matrices on the supersingular nodes together with their degeneracy intertwining in the prime $s$, and the identification of the Frobenius, the node widths and the degeneracy maps with their canonical modular counterparts (arithmetic Frobenius, characteristic widths, restriction of places along the $q$-expansion embeddings). It is the input used by [`CerednikDrinfeld.exists_cartierAnchors_degeneracyDuality_jZero_ssPlaces_correspondence_arithFrobC_restrictAlong_placeWidthChar`](thm.html#CerednikDrinfeld.exists_cartierAnchors_degeneracyDuality_jZero_ssPlaces_correspondence_arithFrobC_restrictAlong_placeWidthChar), and through it serves the level-lowering step of the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_twoLevelSemistableSpecialization_jointConstruction_ssPlaces_heckeTransport_canonical_levelPrimeIntertwine_correspondence_arithFrobC_restrictAlong_placeWidthChar.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_CerednikDrinfeld_Ribbon
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

theorem CerednikDrinfeld.exists_twoLevelSemistableSpecialization_jointConstruction_ssPlaces_heckeTransport_canonical_levelPrimeIntertwine_correspondence_arithFrobC_restrictAlong_placeWidthChar
    (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero q'] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q')
    [DecidableEq (IsLocalRing.ResidueField A)]
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField A))]
    [DecidableEq ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField A))]
    :
    letI := ModularCurve.heckeModuleBar ((M * s) * q')
    letI := ModularCurve.heckeModuleBar (M * s)
    letI := ModularCurve.heckeModuleBar (M * q')
    letI := ModularCurve.heckeModuleBar M
    letI := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (IsLocalRing.ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    ∃ (_ : Module HeckeAlg (AlgebraicCurve.Pic0 (IsLocalRing.ResidueField A)
          (modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))))
      (_ : Module HeckeAlg (AlgebraicCurve.Pic0 (IsLocalRing.ResidueField A)
          (modularFunctionFieldC (IsLocalRing.ResidueField A) M)))
      (D₁ : JZeroSemistableSpecialization A (M * s) q' hq')
      (D₂ : JZeroSemistableSpecialization A M q' hq')
      (ab : Fin 2 → (↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)) →
          ↥(ssPlaces q' M (IsLocalRing.ResidueField A))))
      (e₁ : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)) ≃ ↥D₁.nodes)
      (e₂ : ↥(ssPlaces q' M (IsLocalRing.ResidueField A)) ≃ ↥D₂.nodes)
      (w : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)) → ℕ+)
      (wV : ↥(ssPlaces q' M (IsLocalRing.ResidueField A)) → ℕ+)
      (m : Fin 2 → ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)) → ℕ)
      (dpair : Fin 2 → (JZero ((M * s) * q') →+ JZero (M * q')))
      (Φ : Fin 2 → (AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField A)
            (modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s)) D₁.nodes →+
          AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField A)
            (modularFunctionFieldC (IsLocalRing.ResidueField A) M) D₂.nodes))
      (T₁ : Nat.Primes → Matrix ↥D₁.nodes ↥D₁.nodes ℤ) (n₁ : Nat.Primes → ℤ)
      (T₂ : Nat.Primes → Matrix ↥D₂.nodes ↥D₂.nodes ℤ) (n₂ : Nat.Primes → ℤ),
      D₁.nodes = nodePairsOfPlaces D₁.frob
          (ssPlaces q' (M * s) (IsLocalRing.ResidueField A)).toFinset ∧
      D₂.nodes = nodePairsOfPlaces D₂.frob
          (ssPlaces q' M (IsLocalRing.ResidueField A)).toFinset ∧
      (∀ p, ((e₁ p : ↥D₁.nodes) : AlgebraicCurve.Place (IsLocalRing.ResidueField A)
          (modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s)) ×
          AlgebraicCurve.Place (IsLocalRing.ResidueField A)
          (modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))).1 = ↑p) ∧
      (∀ p, ((e₂ p : ↥D₂.nodes) : AlgebraicCurve.Place (IsLocalRing.ResidueField A)
          (modularFunctionFieldC (IsLocalRing.ResidueField A) M) ×
          AlgebraicCurve.Place (IsLocalRing.ResidueField A)
          (modularFunctionFieldC (IsLocalRing.ResidueField A) M)).1 = ↑p) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero ((M * s) * q'), PrimeToTorsion q' x →
          ∃ h : σ • x - x ∈ inertiaInvariants A ((M * s) * q'),
            D₁.comp ⟨σ • x - x, h⟩ = 0 ∧
              AlgebraicCurve.GluedPic0.toPic0Pair D₁.nodes (D₁.sp ⟨σ • x - x, h⟩) = 0) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero (M * q'), PrimeToTorsion q' x →
          ∃ h : σ • x - x ∈ inertiaInvariants A (M * q'),
            D₂.comp ⟨σ • x - x, h⟩ = 0 ∧
              AlgebraicCurve.GluedPic0.toPic0Pair D₂.nodes (D₂.sp ⟨σ • x - x, h⟩) = 0) ∧
      (∀ (i : Fin 2) (y : JZero ((M * s) * q')),
          y ∈ toricMonodromyPart (J := JZero ((M * s) * q')) q' (A.inertiaSubgroupIn ℚ) →
          dpair i y ∈ toricMonodromyPart (J := JZero (M * q')) q' (A.inertiaSubgroupIn ℚ)) ∧
      (∀ (i : Fin 2) (x : ↥(inertiaInvariants A ((M * s) * q')))
          (hx : dpair i ↑x ∈ inertiaInvariants A (M * q')),
          D₁.comp x = 0 →
          D₂.sp ⟨dpair i ↑x, hx⟩ = Φ i (D₁.sp x)) ∧
      (∀ (i : Fin 2) (p : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))),
          m i p * (w p : ℕ) = (wV (ab i p) : ℕ)) ∧
      (∀ (i : Fin 2) (v : ↥(ssPlaces q' M (IsLocalRing.ResidueField A))),
          (∑ p with ab i p = v, m i p) = s + 1) ∧
      (∀ (i : Fin 2) (g : ↥D₁.nodes → Additive (IsLocalRing.ResidueField A)ˣ),
          Φ i (AlgebraicCurve.GluedPic0.nodeUnit D₁.nodes g) =
            AlgebraicCurve.GluedPic0.nodeUnit D₂.nodes
              (fun n₂ => ∑ p₁ with ab i p₁ = e₂.symm n₂, m i p₁ • g (e₁ p₁))) ∧
      (∀ i : Fin 2, ∀ y : JZero ((M * s) * q'), ∀ z : JZero ((M * q') * s),
          Nat.mul_right_comm M s q' ▸ y = z →
            dpair i y = degeneracyPushforwardPair (M * q') s i z) ∧
      (∀ p : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A)),
          (w p : ℕ) = D₁.width (e₁ p)) ∧
      (∀ v : ↥(ssPlaces q' M (IsLocalRing.ResidueField A)),
          (wV v : ℕ) = D₂.width (e₂ v)) ∧
      ((∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : ModularCurve.JZero ((M * s) * q'),
          ModularCurve.PrimeToTorsion q' x →
            ∃ h : σ • x - x ∈ ModularCurve.inertiaInvariants A ((M * s) * q'),
              D₁.comp ⟨σ • x - x, h⟩ = 0 ∧
                AlgebraicCurve.GluedPic0.toPic0Pair D₁.nodes (D₁.sp ⟨σ • x - x, h⟩) = 0) ∧
        (∀ m : ℕ, m.Coprime q' →
          ∀ g : AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField ↥A)
              ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥A) (M * s)) D₁.nodes,
            (m : ℤ) • g = 0 →
              ∃ x : ↥(ModularCurve.inertiaInvariants A ((M * s) * q')),
                (m : ℤ) • (x : ModularCurve.JZero ((M * s) * q')) = 0 ∧ D₁.comp x = 0 ∧ D₁.sp x = g) ∧
        (∀ m : ℕ, m.Coprime q' →
          ∀ φ : ModularCurve.componentGroup D₁.width, (m : ℤ) • φ = 0 →
            ∃ x : ↥(ModularCurve.inertiaInvariants A ((M * s) * q')),
              (m : ℤ) • (x : ModularCurve.JZero ((M * s) * q')) = 0 ∧ D₁.comp x = φ) ∧
        Function.Surjective D₁.comp ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(ModularCurve.inertiaInvariants A ((M * s) * q')))
            (hx : σ • (x : ModularCurve.JZero ((M * s) * q')) ∈ ModularCurve.inertiaInvariants A ((M * s) * q')),
            D₁.comp x = 0 → D₁.comp ⟨σ • (x : ModularCurve.JZero ((M * s) * q')), hx⟩ = 0) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(ModularCurve.inertiaInvariants A ((M * s) * q')))
            (hx : σ • (x : ModularCurve.JZero ((M * s) * q')) ∈ ModularCurve.inertiaInvariants A ((M * s) * q')),
            D₁.comp x = 0 → AlgebraicCurve.GluedPic0.toPic0Pair D₁.nodes (D₁.sp x) = 0 →
              AlgebraicCurve.GluedPic0.toPic0Pair D₁.nodes
                (D₁.sp ⟨σ • (x : ModularCurve.JZero ((M * s) * q')), hx⟩) = 0) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(ModularCurve.inertiaInvariants A ((M * s) * q')))
            (hx : σ • (x : ModularCurve.JZero ((M * s) * q')) ∈ ModularCurve.inertiaInvariants A ((M * s) * q')),
            D₁.comp x = 0 → ∀ a b : ModularCurve.JZero (M * s),
              AlgebraicCurve.GluedPic0.toPic0Pair D₁.nodes (D₁.sp x) = (D₁.spN a, D₁.spN b) →
                AlgebraicCurve.GluedPic0.toPic0Pair D₁.nodes
                    (D₁.sp ⟨σ • (x : ModularCurve.JZero ((M * s) * q')), hx⟩)
                  = (D₁.spN (σ • a), D₁.spN (σ • b))) ∧
        (∀ s : ↥D₁.nodes, 0 < D₁.width s) ∧
        (∃ _ : Module ModularCurve.HeckeAlg (ModularCurve.componentGroup D₁.width),
          (∀ (T : ModularCurve.HeckeAlg) (x : ↥(ModularCurve.inertiaInvariants A ((M * s) * q')))
            (hx : T • (x : ModularCurve.JZero ((M * s) * q')) ∈ ModularCurve.inertiaInvariants A ((M * s) * q')),
            D₁.comp ⟨T • (x : ModularCurve.JZero ((M * s) * q')), hx⟩ = T • D₁.comp x) ∧
          (∀ 𝔪 : Ideal ModularCurve.HeckeAlg, 𝔪.IsMaximal →
            ModularCurve.heckeTorsion (ModularCurve.componentGroup D₁.width) 𝔪 = ⊥ →
              ∀ x ∈ ModularCurve.heckeTorsion (ModularCurve.JZero ((M * s) * q')) 𝔪,
                ModularCurve.PrimeToTorsion q' x →
                  ∀ h : x ∈ ModularCurve.inertiaInvariants A ((M * s) * q'), D₁.comp ⟨x, h⟩ = 0 →
                    AlgebraicCurve.GluedPic0.toPic0Pair D₁.nodes (D₁.sp ⟨x, h⟩) = 0 →
                      x ∈ ModularCurve.toricMonodromyPart (J := ModularCurve.JZero ((M * s) * q')) q'
                        (A.inertiaSubgroupIn ℚ)))) ∧
      ((∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : ModularCurve.JZero ((M) * q'),
          ModularCurve.PrimeToTorsion q' x →
            ∃ h : σ • x - x ∈ ModularCurve.inertiaInvariants A ((M) * q'),
              D₂.comp ⟨σ • x - x, h⟩ = 0 ∧
                AlgebraicCurve.GluedPic0.toPic0Pair D₂.nodes (D₂.sp ⟨σ • x - x, h⟩) = 0) ∧
        (∀ m : ℕ, m.Coprime q' →
          ∀ g : AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField ↥A)
              ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥A) (M)) D₂.nodes,
            (m : ℤ) • g = 0 →
              ∃ x : ↥(ModularCurve.inertiaInvariants A ((M) * q')),
                (m : ℤ) • (x : ModularCurve.JZero ((M) * q')) = 0 ∧ D₂.comp x = 0 ∧ D₂.sp x = g) ∧
        (∀ m : ℕ, m.Coprime q' →
          ∀ φ : ModularCurve.componentGroup D₂.width, (m : ℤ) • φ = 0 →
            ∃ x : ↥(ModularCurve.inertiaInvariants A ((M) * q')),
              (m : ℤ) • (x : ModularCurve.JZero ((M) * q')) = 0 ∧ D₂.comp x = φ) ∧
        Function.Surjective D₂.comp ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(ModularCurve.inertiaInvariants A ((M) * q')))
            (hx : σ • (x : ModularCurve.JZero ((M) * q')) ∈ ModularCurve.inertiaInvariants A ((M) * q')),
            D₂.comp x = 0 → D₂.comp ⟨σ • (x : ModularCurve.JZero ((M) * q')), hx⟩ = 0) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(ModularCurve.inertiaInvariants A ((M) * q')))
            (hx : σ • (x : ModularCurve.JZero ((M) * q')) ∈ ModularCurve.inertiaInvariants A ((M) * q')),
            D₂.comp x = 0 → AlgebraicCurve.GluedPic0.toPic0Pair D₂.nodes (D₂.sp x) = 0 →
              AlgebraicCurve.GluedPic0.toPic0Pair D₂.nodes
                (D₂.sp ⟨σ • (x : ModularCurve.JZero ((M) * q')), hx⟩) = 0) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(ModularCurve.inertiaInvariants A ((M) * q')))
            (hx : σ • (x : ModularCurve.JZero ((M) * q')) ∈ ModularCurve.inertiaInvariants A ((M) * q')),
            D₂.comp x = 0 → ∀ a b : ModularCurve.JZero (M),
              AlgebraicCurve.GluedPic0.toPic0Pair D₂.nodes (D₂.sp x) = (D₂.spN a, D₂.spN b) →
                AlgebraicCurve.GluedPic0.toPic0Pair D₂.nodes
                    (D₂.sp ⟨σ • (x : ModularCurve.JZero ((M) * q')), hx⟩)
                  = (D₂.spN (σ • a), D₂.spN (σ • b))) ∧
        (∀ s : ↥D₂.nodes, 0 < D₂.width s) ∧
        (∃ _ : Module ModularCurve.HeckeAlg (ModularCurve.componentGroup D₂.width),
          (∀ (T : ModularCurve.HeckeAlg) (x : ↥(ModularCurve.inertiaInvariants A ((M) * q')))
            (hx : T • (x : ModularCurve.JZero ((M) * q')) ∈ ModularCurve.inertiaInvariants A ((M) * q')),
            D₂.comp ⟨T • (x : ModularCurve.JZero ((M) * q')), hx⟩ = T • D₂.comp x) ∧
          (∀ 𝔪 : Ideal ModularCurve.HeckeAlg, 𝔪.IsMaximal →
            ModularCurve.heckeTorsion (ModularCurve.componentGroup D₂.width) 𝔪 = ⊥ →
              ∀ x ∈ ModularCurve.heckeTorsion (ModularCurve.JZero ((M) * q')) 𝔪,
                ModularCurve.PrimeToTorsion q' x →
                  ∀ h : x ∈ ModularCurve.inertiaInvariants A ((M) * q'), D₂.comp ⟨x, h⟩ = 0 →
                    AlgebraicCurve.GluedPic0.toPic0Pair D₂.nodes (D₂.sp ⟨x, h⟩) = 0 →
                      x ∈ ModularCurve.toricMonodromyPart (J := ModularCurve.JZero ((M) * q')) q'
                        (A.inertiaSubgroupIn ℚ)))) ∧
      (∀ (ℓ : Nat.Primes) (s : ↥D₁.nodes), ∑ t : ↥D₁.nodes, T₁ ℓ t s = n₁ ℓ) ∧
      (∀ ℓ : Nat.Primes,
        ∀ (x : ↥(inertiaInvariants A ((M * s) * q')))
          (hx : heckeGen ℓ • (x : JZero ((M * s) * q')) ∈ inertiaInvariants A ((M * s) * q')),
          D₁.comp x = 0 →
          ∀ w : ↥D₁.nodes → Additive (IsLocalRing.ResidueField A)ˣ,
            D₁.sp x = AlgebraicCurve.GluedPic0.nodeUnit D₁.nodes w →
              D₁.sp ⟨heckeGen ℓ • (x : JZero ((M * s) * q')), hx⟩ =
                AlgebraicCurve.GluedPic0.nodeUnit D₁.nodes
                  (fun t => ∑ s : ↥D₁.nodes, T₁ ℓ s t • w s)) ∧
      (∀ (ℓ : Nat.Primes) (s : ↥D₂.nodes), ∑ t : ↥D₂.nodes, T₂ ℓ t s = n₂ ℓ) ∧
      (∀ ℓ : Nat.Primes,
        ∀ (x : ↥(inertiaInvariants A (M * q')))
          (hx : heckeGen ℓ • (x : JZero (M * q')) ∈ inertiaInvariants A (M * q')),
          D₂.comp x = 0 →
          ∀ w : ↥D₂.nodes → Additive (IsLocalRing.ResidueField A)ˣ,
            D₂.sp x = AlgebraicCurve.GluedPic0.nodeUnit D₂.nodes w →
              D₂.sp ⟨heckeGen ℓ • (x : JZero (M * q')), hx⟩ =
                AlgebraicCurve.GluedPic0.nodeUnit D₂.nodes
                  (fun t => ∑ s : ↥D₂.nodes, T₂ ℓ s t • w s)) ∧
      (∀ ℓ ℓ' : Nat.Primes, Commute (T₁ ℓ) (T₁ ℓ')) ∧
      (∀ ℓ ℓ' : Nat.Primes, Commute (T₂ ℓ) (T₂ ℓ')) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ (M * s) * q' → n₁ ℓ = ((ℓ : ℕ) : ℤ) + 1) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M * q' → n₂ ℓ = ((ℓ : ℕ) : ℤ) + 1) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ (M * s) * q' →
          ∀ i j : ↥D₁.nodes, (D₁.width i : ℤ) * T₁ ℓ i j = (D₁.width j : ℤ) * T₁ ℓ j i) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M * q' →
          ∀ i j : ↥D₂.nodes, (D₂.width i : ℤ) * T₂ ℓ i j = (D₂.width j : ℤ) * T₂ ℓ j i) ∧
      (∀ i j, T₁ ⟨q', hq'⟩ (e₁ i) (e₁ j) =
          if i = e₁.symm
              ((AlgebraicCurve.SemilinearAut.nodePerm D₁.nodes D₁.frob D₁.frob_nodeStable).symm (e₁ j))
          then 1 else 0) ∧
      (∀ i j, T₂ ⟨q', hq'⟩ (e₂ i) (e₂ j) =
          if i = e₂.symm
              ((AlgebraicCurve.SemilinearAut.nodePerm D₂.nodes D₂.frob D₂.frob_nodeStable).symm (e₂ j))
          then 1 else 0) ∧
      (∀ (i : Fin 2) (ℓ : Nat.Primes), (ℓ : ℕ) ≠ s →
          degeneracyMatrix (ab i) * (T₁ ℓ).submatrix ⇑e₁ ⇑e₁ =
            (T₂ ℓ).submatrix ⇑e₂ ⇑e₂ * degeneracyMatrix (ab i)) ∧
      (degeneracyMatrix (ab 1) * (T₁ ⟨s, hs⟩).submatrix ⇑e₁ ⇑e₁ =
          (T₂ ⟨s, hs⟩).submatrix ⇑e₂ ⇑e₂ * degeneracyMatrix (ab 1) - degeneracyMatrix (ab 0)) ∧
      (degeneracyMatrix (ab 0) * (T₁ ⟨s, hs⟩).submatrix ⇑e₁ ⇑e₁ = (s : ℤ) • degeneracyMatrix (ab 1)) ∧
      (∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q' →
          (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
            ∀ [AlgebraicCurve.HasPrincipalDivisors (IsLocalRing.ResidueField A)
                (ModularCurve.charLDegeneracyRoof (IsLocalRing.ResidueField A) (M * s) ℓ)]
              (hαc : ModularCurve.HeckeAlphaCIntegral (IsLocalRing.ResidueField A) (M * s) ℓ)
              (hβc : ModularCurve.HeckeBetaCIntegral (IsLocalRing.ResidueField A) (M * s) ℓ)
              (a b : ↥D₁.nodes),
              T₁ ℓ a b = AlgebraicCurve.Divisor.correspondence
                (ModularCurve.heckeAlphaC (IsLocalRing.ResidueField A) (M * s) ℓ)
                (ModularCurve.heckeBetaC (IsLocalRing.ResidueField A) (M * s) ℓ) hαc hβc
                (Finsupp.single b.1.1 1) a.1.1)) ∧
      (∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q' →
          (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
            ∀ [AlgebraicCurve.HasPrincipalDivisors (IsLocalRing.ResidueField A)
                (ModularCurve.charLDegeneracyRoof (IsLocalRing.ResidueField A) M ℓ)]
              (hαc : ModularCurve.HeckeAlphaCIntegral (IsLocalRing.ResidueField A) M ℓ)
              (hβc : ModularCurve.HeckeBetaCIntegral (IsLocalRing.ResidueField A) M ℓ)
              (a b : ↥D₂.nodes),
              T₂ ℓ a b = AlgebraicCurve.Divisor.correspondence
                (ModularCurve.heckeAlphaC (IsLocalRing.ResidueField A) M ℓ)
                (ModularCurve.heckeBetaC (IsLocalRing.ResidueField A) M ℓ) hαc hβc
                (Finsupp.single b.1.1 1) a.1.1)) ∧
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
      (∀ v : ↥(ssPlaces q' M (IsLocalRing.ResidueField A)), (wV v : ℕ) = placeWidthChar q' M v.1) ∧
      D₁.frob = arithFrobC q' (IsLocalRing.ResidueField A) (M * s) ∧
      D₂.frob = arithFrobC q' (IsLocalRing.ResidueField A) M := by sorry
