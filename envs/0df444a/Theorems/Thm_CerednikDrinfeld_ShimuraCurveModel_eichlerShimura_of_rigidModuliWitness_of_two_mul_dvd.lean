-- Prove2me | Theorems.Thm_CerednikDrinfeld_ShimuraCurveModel_eichlerShimura_of_rigidModuliWitness_of_two_mul_dvd
-- name    : CerednikDrinfeld.ShimuraCurveModel.eichlerShimura_of_rigidModuliWitness_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/7fe7e08e-ae9a-5cc6-a8d3-f7ff2781799f
-- title:
--   Eichler–Shimura congruence on J[p] for a Shimura curve
-- statement:
--   Fix a squarefree $N$ with $N \neq 0$, primes $q \neq q'$ with $q, q' \geq 5$, neither dividing $N$, and an integer $D$ divisible by $2Nqq'$. Let $\mathbb{H}[\mathbb{Q},a,b]$ satisfy `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra at $v$ has all nonzero elements invertible exactly when $q \in v$ or $q' \in v$; let $R$ be an Eichler order of level $N$ (an intersection of two maximal orders, of relative index $N$ in one of them), $\iota$ an injective $\mathbb{Q}$-algebra map to $M_2(\mathbb{R})$, and $\Lambda \supseteq R$ a maximal order. Let $M$ be a `ShimuraCurveModel` for $R$, $\iota$ and the Hecke sets $\ell \mapsto$ `levelHeckeUSet Λ R ℓ` for $\ell \mid N$ and `primeHeckeSet R ℓ` otherwise, and $w$ a `ModuliWitnessD` for $M$, $\Lambda$, $N$, $q$, $q'$, $D$ with integral total space, which is a good-reduction model ($\pi_X$ smooth of relative dimension $1$ and all geometric fibres over $\mathbb{Z}[1/D]$ integral). Assume further: every fake elliptic curve over $\overline{\mathbb{Q}}$ with $\Lambda$-action and level $N$ descends, up to pullback, to any valuation subring in which $Nqq'$ is invertible (`hlift`); for every prime $\ell \nmid D$ and every place $P$ in the image of a fake elliptic curve, $M$'s place correspondence `corrBar ℓ` sends $[P]$ to the sum of the $\ell+1$ points attached to the quotients by the $\ell+1$ pairwise distinct extra level structures of $E$, each an $\ell$-level isogeny (`hmult`); and a curve model $\mathfrak{M}$ of $M.\mathrm{Fbar}$ over $\overline{\mathbb{Q}}$ isomorphic to the pullback of $\pi_X$ along $\bar{s}$, whose point–place dictionary is $w.\mathrm{pts}$ and whose function-field identification extends $w.e_F$ through $M.\mathrm{toBar}$ (`hpts`). Finally fix signs $\varepsilon$ trivial away from $q, q'$, tower data $\mathbb{T}$ of Hecke type for $q, q'$ over $M.\mathrm{Fbar}$ whose function fields are finitely generated of transcendence degree one, semilinear Galois actions `galT` with base action the given automorphism and compatible with the tower maps, and commuting involutions $W_0, W_1$ on $M.\mathrm{Fbar}$ and $W_{\ell,0}, W_{\ell,1}$ on each tower field, all trivial on $\overline{\mathbb{Q}}$, commuting with Galois and with the tower maps, such that $W_0$ and $W_1$ act on $M.J$ as $\varepsilon_q$ times the Picard Hecke operator at $q$ and $\varepsilon_{q'}$ times that at $q'$, act on places as `corrBar q` and `corrBar q'`, that the degrees of the tower maps are $\ell$ for $\ell \mid N$ and $\ell+1$ otherwise, and that for every prime $\ell \neq q, q'$ the correspondence `corrBar ℓ` on divisors is pullback along $\varphi_{\ell,0}$ followed by pushforward along $\varphi_{\ell,1}$. The conclusion: for every prime $p$, every prime $\ell$ with $\ell \nmid Dp$, every valuation subring $B$ of $\overline{\mathbb{Q}}$ in which $\ell$ is a nonunit, every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lying in the decomposition subgroup of $B$ and acting on its residue field by $x \mapsto x^{\ell}$, and every $t \in M.J$ with $pt = 0$, one has $\sigma^2 t - T_{\ell}(\sigma t) + \ell t = 0$, where $\sigma$ acts through `M.galJ` and $T_\ell$ is `M.heckeJ (heckeGen ⟨ℓ, hℓ⟩)`.
--
--   This is the Eichler–Shimura congruence relation for the Shimura curve attached to an Eichler order of level $N$ in the quaternion algebra ramified exactly at $q$ and $q'$, in the form of the quadratic relation $\sigma^2 - T_\ell \sigma + \ell$ on the $p$-torsion of the degree-zero Picard group at a Frobenius element above a prime $\ell$ of good reduction. It is one of the two conjuncts of the good-reduction-outside-$Nqq'p$ package for such models, and is used by `goodReductionOutside_of_rigidModuliWitness_heckeTower_of_two_mul_dvd`, which feeds the Galois-representation input to level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ShimuraCurveModel_eichlerShimura_of_rigidModuliWitness_of_two_mul_dvd.lean

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

theorem CerednikDrinfeld.ShimuraCurveModel.eichlerShimura_of_rigidModuliWitness_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    (M : ShimuraCurveModel R ι (fun ℓ => if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ))
    (w : M.ModuliWitnessD Λ N q q' D) (hgood : w.IsGoodReductionModel)

    (hlift : ∀ (B : ValuationSubring (AlgebraicClosure ℚ)), IsUnit (((N * q * q' : ℕ) : ℤ) : ↥B) →
      ∀ E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ), ∃ 𝒜 : CerednikDrinfeld.QM.FakeEllipticCurve Λ N ↥B,
        CerednikDrinfeld.QM.FakeEllipticCurve.IsPullback (B.subtype : ↥B →+* AlgebraicClosure ℚ) 𝒜 E)

    (hmult : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ D →
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
            Finset.univ.sum (fun i : Fin (ℓ + 1) => Finsupp.single (w.pts.symm (w.pt _ w.sbar (d i))) 1))

    [hXint : AlgebraicGeometry.IsIntegral w.X]
    (hpts : ∃ (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) M.Fbar)
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
          M.toBar (w.eF.symm (w.X.germToFunctionField U t))))
    (ε : Nat.Primes → ℤˣ) (hε : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q → (ℓ : ℕ) ≠ q' → ε ℓ = 1)
    (𝕋 : HeckeTower.TowerData q q' M.Fbar)
    (hfg : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) M.Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (hgalT_base : ∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galT ℓ σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (hgalT_φ : ∀ (α : HeckeTower.Arr q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M.Fbar),
      galT α.1 σ • 𝕋.φ α x = 𝕋.φ α (M.gal σ • x))
    (hW_base : ∀ i (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (W i) a = a)
    (hWT_base : ∀ ℓ i (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (WT ℓ i) a = a)
    (hW_sq : ∀ i, W i * W i = 1)
    (hW_comm : W 0 * W 1 = W 1 * W 0)
    (hW_gal : ∀ i σ, W i * M.gal σ = M.gal σ * W i)
    (hWT_sq : ∀ ℓ i, WT ℓ i * WT ℓ i = 1)
    (hWT_comm : ∀ ℓ, WT ℓ 0 * WT ℓ 1 = WT ℓ 1 * WT ℓ 0)
    (hWT_gal : ∀ ℓ i σ, WT ℓ i * galT ℓ σ = galT ℓ σ * WT ℓ i)
    (hWT_φ : ∀ (α : HeckeTower.Arr q q') i (x : M.Fbar), WT α.1 i • 𝕋.φ α x = 𝕋.φ α (W i • x))
    (hW0_pic : ∀ c : M.J, W 0 • c = ((ε ⟨q, Fact.out⟩ : ℤˣ) : ℤ) • M.heckePic0 q Fact.out c)
    (hW1_pic : ∀ c : M.J, W 1 • c = ((ε ⟨q', Fact.out⟩ : ℤˣ) : ℤ) • M.heckePic0 q' Fact.out c)
    (hW0_pl : ∀ P : Place (AlgebraicClosure ℚ) M.Fbar, M.corrBar q Fact.out (Finsupp.single P 1) = Finsupp.single (W 0 • P) 1)
    (hW1_pl : ∀ P : Place (AlgebraicClosure ℚ) M.Fbar, M.corrBar q' Fact.out (Finsupp.single P 1) = Finsupp.single (W 1 • P) 1)
    (hdeg : ∀ α : HeckeTower.Arr q q', finrankAlong (AlgebraicClosure ℚ) (𝕋.φ α) = HeckeTower.arrowDegree N α)
    (hhecke : ∀ (ℓ : HeckeTower.AwayPrime q q') (Dv : Divisor (AlgebraicClosure ℚ) M.Fbar),
      M.corrBar ℓ.1 ℓ.1.prop Dv = Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) Dv)
    :
    ∀ p : ℕ, p.Prime → ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ D * p →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt σ ℓ →
          ∀ t : M.J, p • t = 0 →
            M.galJ σ (M.galJ σ t) - M.heckeJ (heckeGen ⟨ℓ, hℓ⟩) (M.galJ σ t) + ℓ • t = 0 := by sorry
