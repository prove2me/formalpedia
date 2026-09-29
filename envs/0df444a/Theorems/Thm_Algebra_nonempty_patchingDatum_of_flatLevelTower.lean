-- Prove2me | Theorems.Thm_Algebra_nonempty_patchingDatum_of_flatLevelTower
-- name    : Algebra.nonempty_patchingDatum_of_flatLevelTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/226e049c-fe4c-5d5a-b6bb-3a1b2b0c3e0c
-- title:
--   Flat Taylor–Wiles level tower assembles into a patching datum
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring with finite residue field, let $p$ be a prime lying in the maximal ideal of $\mathcal O$, let $r$ be a natural number, and let $\bar\rho$ be a residual Galois representation over the residue field of $\mathcal O$ (a two-dimensional space with an action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ factoring through a finite level). Let $S_{\min}$ be a finite set of natural numbers containing $p$, all of whose members are prime, and let $Q\colon\mathbb N\to\mathrm{Finset}\,\mathbb N$ be arbitrary. Let $D_{\min}$ be a deformation-ring datum for $\bar\rho$ for the minimal flat condition at $S_{\min}$ (cyclotomic determinant, flat at $p$, unramified at all primes outside $S_{\min}$, and characteristic polynomial $(X-1)^2$ on inertia at each prime of $S_{\min}$ other than $p$), and for each $n$ let $D_{Q_n}$ be such a datum for the flat condition at $S_{\min}\cup Q_n$ together with the same unipotence on inertia at the primes of $S_{\min}$ other than $p$; write $R_{\min}=D_{\min}.R$ and $R_n=(D_{Q_n}).R$ for the associated complete Noetherian local $\mathcal O$-algebras carrying universal deformations. Let $T$ be a commutative $\mathcal O$-algebra, $M$ a nontrivial $T$-module which is also an $R_{\min}$-module, and $\theta\colon R_{\min}\to T$ an $\mathcal O$-algebra map with $x\cdot m=\theta(x)\cdot m$. Suppose given exponents $k(n,i)\ge n$ for $i<r$; surjective $\mathcal O$-algebra maps $\gamma_n$ from $\mathcal O[[X_1,\dots,X_r]]$ onto $R_n$; $\mathcal O$-algebra maps $\iota_n$ from the group algebra $\Lambda_n=\mathcal O[\prod_{i<r}\mathbb Z/p^{k(n,i)}]$ to $R_n$; surjective $\mathcal O$-algebra maps $\varepsilon_n\colon R_n\to R_{\min}$ sending $\iota_n(g)$ to $1$ for every group element $g$; $R_n$-modules $M_n$ with elements $b_{n,1},\dots,b_{n,d(n)}$ that span $M_n$ over $\Lambda_n$ through $\iota_n$ and admit no nontrivial $\Lambda_n$-relation; and surjective additive maps $\lambda_n\colon M_n\to M$ with $\lambda_n(x\cdot m)=\varepsilon_n(x)\cdot\lambda_n(m)$ whose kernel is exactly $(\iota_n(\ker\text{(augmentation of }\Lambda_n))\,)\cdot M_n$. The conclusion is that [`Algebra.PatchingDatum 𝒪 p r R_min M`](def/Algebra_PatchingDatum.html#L39) is nonempty: for every $n$ there are a module $N$ over $\mathcal O[[X_1,\dots,X_r]]$, an $\mathcal O$-algebra endomorphism $\varphi$ of that power series ring, a surjection $\psi$ onto $R_{\min}$ with $\psi(\varphi(X_i))=0$, a surjective additive $\pi\colon N\to M$ semilinear along $\psi$ with kernel $(\varphi(X_1),\dots,\varphi(X_r))N$, and finitely many elements of $N$ spanning $N$ over $\varphi$ whose relation ideal is exactly $\big((1+X_j)^{p^n}-1\big)_j$.
--
--   This is the flat-deformation form of the input to the Taylor–Wiles patching argument: the level-$Q_n$ deformation rings, their group-algebra structure coming from inertia at the auxiliary primes, and the Hecke modules free over those group algebras and descending to the minimal level, are repackaged as the abstract patching datum over $R_{\min}$ and $M$. It is used by the Hecke-algebra statements that produce a patching datum for a residually modular representation in the semistable (flat) case, from which freeness of $M$ and the identification of $R_{\min}$ with the Hecke algebra are extracted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_nonempty_patchingDatum_of_flatLevelTower.lean

import Definitions.Def_Algebra_PatchingDatum
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.nonempty_patchingDatum_of_flatLevelTower
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {p : ℕ} [Fact p.Prime] (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (r : ℕ)
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    (Smin : Finset ℕ) (hpSmin : p ∈ Smin) (hSminPrime : ∀ q ∈ Smin, q.Prime)
    (Q : ℕ → Finset ℕ)
    (Dmin : GaloisRep.DeformationRingData 𝒪 ρbar
      (GaloisRep.minimalFlatCondition 𝒪 p Smin))
    (DQ : ∀ n : ℕ, GaloisRep.DeformationRingData 𝒪 ρbar
      (fun _A _ _ _ ρ => GaloisRep.flatCondition 𝒪 p (Smin ∪ Q n) ρ ∧
        ∀ q ∈ Smin, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q))
    (T : Type) [CommRing T] [Algebra 𝒪 T]
    (M : Type) [AddCommGroup M] [Module T M] [Nontrivial M]
    (θ : Dmin.R →ₐ[𝒪] T) [Module Dmin.R M]
    (hθM : ∀ (x : Dmin.R) (m : M), x • m = θ x • m)
    (k : ℕ → Fin r → ℕ) (hk : ∀ n i, n ≤ k n i)
    (γ : ∀ n, MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] (DQ n).R)
    (hγ : ∀ n, Function.Surjective (γ n))
    (ι : ∀ n, MonoidAlgebra 𝒪
      (Π i : Fin r, Multiplicative (ZMod (p ^ k n i))) →ₐ[𝒪] (DQ n).R)
    (ε : ∀ n, (DQ n).R →ₐ[𝒪] Dmin.R) (hε : ∀ n, Function.Surjective (ε n))
    (hει : ∀ n (g : Π i : Fin r, Multiplicative (ZMod (p ^ k n i))),
      ε n (ι n (MonoidAlgebra.of 𝒪 _ g)) = 1)
    (Mn : ℕ → Type) [∀ n, AddCommGroup (Mn n)] [∀ n, Module ((DQ n).R) (Mn n)]
    (d : ℕ → ℕ) (b : ∀ n, Fin (d n) → Mn n)
    (hspan : ∀ n (x : Mn n),
      ∃ c : Fin (d n) → MonoidAlgebra 𝒪 (Π i : Fin r, Multiplicative (ZMod (p ^ k n i))),
        x = ∑ i, ι n (c i) • b n i)
    (hrel : ∀ n (c : Fin (d n) →
        MonoidAlgebra 𝒪 (Π i : Fin r, Multiplicative (ZMod (p ^ k n i)))),
      ∑ i, ι n (c i) • b n i = 0 ↔ ∀ i, c i = 0)
    (lam : ∀ n, Mn n →+ M)
    (hlam_smul : ∀ n (x : (DQ n).R) (m : Mn n), lam n (x • m) = ε n x • lam n m)
    (hlam_surj : ∀ n, Function.Surjective (lam n))
    (hlam_ker : ∀ n (m : Mn n), lam n m = 0 ↔ m ∈
      (Ideal.map (ι n) (RingHom.ker (Bialgebra.counitAlgHom 𝒪
        (MonoidAlgebra 𝒪 (Π i : Fin r, Multiplicative (ZMod (p ^ k n i))))))) •
        (⊤ : Submodule ((DQ n).R) (Mn n))) :
    Nonempty (Algebra.PatchingDatum 𝒪 p r Dmin.R M) := by sorry
