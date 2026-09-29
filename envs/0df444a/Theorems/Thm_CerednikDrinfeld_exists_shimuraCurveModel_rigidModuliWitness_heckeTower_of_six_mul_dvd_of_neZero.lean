-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_shimuraCurveModel_rigidModuliWitness_heckeTower_of_six_mul_dvd_of_neZero
-- name    : CerednikDrinfeld.exists_shimuraCurveModel_rigidModuliWitness_heckeTower_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/8e583ba2-b208-5b34-896d-f37f62ea00bc
-- title:
--   Canonical model, moduli witness and Hecke tower for X₀^{qq'}(N)
-- statement:
--   Let $N$ be a non-zero squarefree natural number, let $q\neq q'$ be primes with $q,q'\geq 5$ neither dividing $N$, and let $D$ be a non-zero natural number with $6Nqq'\mid D$. Let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q\in v$ or $q'\in v$. Let $R$ be a $\mathbb{Z}$-submodule which is an Eichler order of level $N$ (an intersection $\Lambda_1\cap\Lambda_2$ of two maximal orders with $[\Lambda_1:R]=N$), and $\iota$ an injective $\mathbb{Q}$-algebra map $\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$. The assertion is that there exist a maximal order $\Lambda\supseteq R$, a `ShimuraCurveModel` $M$ for $R$, $\iota$ and the Hecke sets $\ell\mapsto$ `levelHeckeUSet Λ R ℓ` for $\ell\mid N$ and `primeHeckeSet R ℓ` otherwise, and a witness $w:$ `M.ModuliWitnessD Λ N q q' D` (a smooth proper integral $X$ over $\mathbb{Z}[1/D]$ coarsely representing fake elliptic curves with $\Lambda$-action and level-$N$ structure, with $M.F\cong K(X)$ and places of $M.\mathrm{Fbar}$ in bijection with the $\bar{\mathbb{Q}}$-points of $X$), such that: $w$ is oriented (for primes $\ell\mid N$, $Q$ lies in the support of `M.corrBar ℓ` applied to $\delta_P$ exactly when the corresponding fake elliptic curves are joined by an $\ell$-level isogeny) and is a good-reduction model ($\pi_X$ smooth of relative dimension one, with integral geometric fibres); every fake elliptic curve over $\bar{\mathbb{Q}}$ descends to a pullback over each valuation subring $B\subseteq\bar{\mathbb{Q}}$ in which $Nqq'$ is a unit; for each prime $\ell\nmid D$ and each $\bar{\mathbb{Q}}$-point $E$ above a place $P$ there are $\ell+1$ extra level-$\ell$ structures on $E$, pairwise distinguished by the points factoring through them, with $\ell$-level isogeny quotients $d_i$ such that `M.corrBar ℓ` sends $\delta_P$ to $\sum_i\delta_{d_i}$; there is a `CurveModel` $\mathfrak{M}$ over $\bar{\mathbb{Q}}$ with function field $M.\mathrm{Fbar}$, together with an isomorphism of $\mathfrak{M}.C$ with the base change of $X$ along $w.\mathrm{sbar}$, over $\mathrm{Spec}\,\bar{\mathbb{Q}}$, matching $\bar{\mathbb{Q}}$-points with places through $w.\mathrm{pts}$ and germs of functions through $w.e_F$ and $M.\mathrm{toBar}$; and there exist signs $\varepsilon:\text{primes}\to\mathbb{Z}^\times$, equal to $1$ away from $q,q'$, a Hecke tower $\mathbb{T}$ of curve fields $\mathbb{T}.F_\ell$ over $\bar{\mathbb{Q}}$ with two finite integral maps $\mathbb{T}.\varphi(\ell,i)$ from $M.\mathrm{Fbar}$ for each prime $\ell\notin\{q,q'\}$, each tower field being finite over $\bar{\mathbb{Q}}(x)$ for some transcendental $x$, semilinear Galois actions $\mathrm{galT}_\ell$ lifting $\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ and compatible with $M.\mathrm{gal}$ along the $\varphi$, and $\bar{\mathbb{Q}}$-linear involutions $W_0,W_1$ on $M.\mathrm{Fbar}$ and $WT_{\ell,i}$ on $\mathbb{T}.F_\ell$ which commute with each other and with the Galois actions and are intertwined by the $\varphi$, such that $W_0$ acts on `M.J` as $\varepsilon(q)$ times `M.heckePic0 q` and $W_1$ as $\varepsilon(q')$ times `M.heckePic0 q'`, `M.corrBar q` and `M.corrBar q'` send $\delta_P$ to $\delta_{W_0P}$ and $\delta_{W_1P}$, each $\mathbb{T}.\varphi(\ell,i)$ has degree $\ell$ if $\ell\mid N$ and $\ell+1$ otherwise, and for $\ell\notin\{q,q'\}$ the operator `M.corrBar ℓ` on divisors equals the correspondence attached to the pair $\mathbb{T}.\varphi(\ell,0),\mathbb{T}.\varphi(\ell,1)$.
--
--   This packages the canonical model of the Shimura curve attached to an Eichler order of squarefree level $N$ in the indefinite quaternion algebra ramified exactly at $q$ and $q'$, together with its interpretation as a coarse moduli space of fake elliptic curves, its good-reduction model over $\mathbb{Z}[1/D]$, the Atkin–Lehner involutions at $q$ and $q'$, and the tower of Hecke correspondences realising the $T_\ell$ and $U_\ell$ operators. It is the source of the canonical-model data for the Čerednik–Drinfeld interchange step, and is used by [`CerednikDrinfeld.exists_shimuraCurveModel_rigidOrientedModuliWitness_heckeTower_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_shimuraCurveModel_rigidOrientedModuliWitness_heckeTower_of_six_mul_dvd_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_shimuraCurveModel_rigidModuliWitness_heckeTower_of_six_mul_dvd_of_neZero.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_CerednikDrinfeld_DescentIntertwiningBase
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMModuliPropsD
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve
open AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

theorem CerednikDrinfeld.exists_shimuraCurveModel_rigidModuliWitness_heckeTower_of_six_mul_dvd_of_neZero
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 6 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    :
    ∃ (Λ : Submodule ℤ ℍ[ℚ, a, b]) (_ : IsMaximalOrder Λ) (_ : R ≤ Λ),
    ∃ M : ShimuraCurveModel R ι (fun ℓ => if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
      ∃ w : M.ModuliWitnessD Λ N q q' D, w.IsOriented ∧ w.IsGoodReductionModel ∧
      (∀ (B : ValuationSubring (AlgebraicClosure ℚ)), IsUnit (((N * q * q' : ℕ) : ℤ) : ↥B) →
      ∀ E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ), ∃ 𝒜 : CerednikDrinfeld.QM.FakeEllipticCurve Λ N ↥B,
        CerednikDrinfeld.QM.FakeEllipticCurve.IsPullback (B.subtype : ↥B →+* AlgebraicClosure ℚ) 𝒜 E) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ D →
      ∀ (P : Place (AlgebraicClosure ℚ) M.Fbar) (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
        w.pt _ w.sbar E = w.pts P →
        ∃ (K : Fin (ℓ + 1) → E.ExtraLevel ℓ) (d : Fin (ℓ + 1) → CerednikDrinfeld.QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
          (∀ i j : Fin (ℓ + 1),
              (∀ x : NeronModelInfra.SchemeHomOver (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
                CerednikDrinfeld.QM.FactorsThrough (K i).levK x ↔ CerednikDrinfeld.QM.FactorsThrough (K j).levK x) → i = j) ∧
          (∀ i : Fin (ℓ + 1),
              CerednikDrinfeld.QM.FakeEllipticCurve.IsLevelIsogeny ℓ
                (⟨E, K i⟩ : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) (d i)) ∧
          M.corrBar ℓ hℓ (Finsupp.single P 1) =
            Finset.univ.sum (fun i : Fin (ℓ + 1) => Finsupp.single (w.pts.symm (w.pt _ w.sbar (d i))) 1)) ∧

      (haveI : AlgebraicGeometry.IsIntegral w.X := w.isIntegral; ∃ (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) M.Fbar)
        (e𝔐 : Quiver.Hom 𝔐.C (CategoryTheory.Limits.pullback w.πX w.sbar)) (_ : CategoryTheory.IsIso e𝔐),
        CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.snd w.πX w.sbar) = 𝔐.toBase ∧
        (∀ x : {p : Quiver.Hom (AlgebraicGeometry.Spec (CommRingCat.of (AlgebraicClosure ℚ))) 𝔐.C //
            CategoryTheory.CategoryStruct.comp p 𝔐.toBase =
              CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of (AlgebraicClosure ℚ)))},
          (w.pts (𝔐.pointEquivPlace x)).1 =
            CategoryTheory.CategoryStruct.comp x.1
              (CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar))) ∧
        (∀ (U : w.X.Opens) [Nonempty (AlgebraicGeometry.Scheme.Opens.toScheme U)]
          [Nonempty (AlgebraicGeometry.Scheme.Opens.toScheme
            ((TopologicalSpace.Opens.map
              (CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar)).base).obj U))]
          (t : w.X.presheaf.obj (Opposite.op U)),
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField
            ((TopologicalSpace.Opens.map
              (CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar)).base).obj U)
            (((CategoryTheory.CategoryStruct.comp e𝔐 (CategoryTheory.Limits.pullback.fst w.πX w.sbar)).app U).hom t)) =
          M.toBar (w.eF.symm (w.X.germToFunctionField U t)))) ∧
      ∃ ε : Nat.Primes → ℤˣ, (∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q → (ℓ : ℕ) ≠ q' → ε ℓ = 1) ∧

      ∃ (𝕋 : HeckeTower.TowerData q q' M.Fbar)

        (_ : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
          FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))

        (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

        (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) M.Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ)),
        (∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          SemilinearAut.baseAut (galT ℓ σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)) ∧
        (∀ (α : HeckeTower.Arr q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M.Fbar),
          galT α.1 σ • 𝕋.φ α x = 𝕋.φ α (M.gal σ • x)) ∧
        (∀ i (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (W i) a = a) ∧ (∀ ℓ i (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (WT ℓ i) a = a) ∧
        (∀ i, W i * W i = 1) ∧ W 0 * W 1 = W 1 * W 0 ∧ (∀ i σ, W i * M.gal σ = M.gal σ * W i) ∧
        (∀ ℓ i, WT ℓ i * WT ℓ i = 1) ∧ (∀ ℓ, WT ℓ 0 * WT ℓ 1 = WT ℓ 1 * WT ℓ 0) ∧ (∀ ℓ i σ, WT ℓ i * galT ℓ σ = galT ℓ σ * WT ℓ i) ∧
        (∀ (α : HeckeTower.Arr q q') i (x : M.Fbar), WT α.1 i • 𝕋.φ α x = 𝕋.φ α (W i • x)) ∧

        (∀ c : M.J, W 0 • c = ((ε ⟨q, Fact.out⟩ : ℤˣ) : ℤ) • M.heckePic0 q Fact.out c) ∧
        (∀ c : M.J, W 1 • c = ((ε ⟨q', Fact.out⟩ : ℤˣ) : ℤ) • M.heckePic0 q' Fact.out c) ∧

        (∀ P : Place (AlgebraicClosure ℚ) M.Fbar, M.corrBar q Fact.out (Finsupp.single P 1) = Finsupp.single (W 0 • P) 1) ∧
        (∀ P : Place (AlgebraicClosure ℚ) M.Fbar, M.corrBar q' Fact.out (Finsupp.single P 1) = Finsupp.single (W 1 • P) 1) ∧

        (∀ α : HeckeTower.Arr q q', finrankAlong (AlgebraicClosure ℚ) (𝕋.φ α) = HeckeTower.arrowDegree N α) ∧
        (∀ (ℓ : HeckeTower.AwayPrime q q') (Dv : Divisor (AlgebraicClosure ℚ) M.Fbar),
          M.corrBar ℓ.1 ℓ.1.prop Dv = Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) Dv) := by sorry
