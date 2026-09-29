-- Prove2me | Theorems.Thm_CuspForm_heckeLocal_exists_heckeModules_levelRaising_and_linearEquiv_baseML_of_isEis_kernel_pair_of_not_cube_dvd
-- name    : CuspForm.heckeLocal.exists_heckeModules_levelRaising_and_linearEquiv_baseML_of_isEis_kernel_pair_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/dba566fb-ad08-5dfa-903a-ad8a73c144d6
-- title:
--   Hecke modules along a cube-free level-raising ladder
-- statement:
--   Let $\mathcal O$ be a characteristic-zero complete discrete valuation ring with finite residue field, $p$ an odd prime with $p\in\mathfrak m_{\mathcal O}$, and $\bar\rho$ an absolutely irreducible two-dimensional residual Galois representation over the residue field of $\mathcal O$ (absolute irreducibility meaning irreducibility after base change to an algebraic closure). Let $S\supseteq S_{\min}\ni p$ be finite sets of primes such that for primes $q\neq p$ one has $q\in S_{\min}$ iff $\bar\rho$ is ramified at $q$, and such that inertia at every $q\in S_{\min}\setminus\{p\}$ acts with characteristic polynomial $(X-1)^2$. Let $n\in\mathbb N$, levels $N_k=$ `Nf k` and rung primes $q_k=$ `qf k` satisfy: all prime factors of every $N_k$ lie in $S$; for $k\le n$, $p^2\nmid N_k$ and $p\mid N_k$ iff $p\mid N_n$; every $q\in S_{\min}\setminus\{p\}$ divides $N_k$; a prime $q\neq p$ outside $S_{\min}$ dividing $N_k$ divides it twice; no prime $q\neq p$ has $q^3\mid N_k$; $N_n$ is squarefree with prime factors other than $p$ exactly those of $S_{\min}$; and for each $k<n$, $q_k\in S$ is a prime $\neq p$ with $N_k=N_{k+1}q_k^2$ and $q_k\nmid N_{k+1}$, or $N_k=N_{k+1}q_k$ with $q_k\,\|\,N_{k+1}$, or $N_k=N_{k+1}q_k$ with $q_k^2\mid N_{k+1}$. At each rung with $q_k^2\nmid N_{k+1}$, Ihara's lemma is assumed in the form: for every $\mathcal O$-module $A$ without $q_k$-torsion, every level $M$ with $q_k\nmid M$, every auxiliary prime $\ell_0\nmid Mq_k$ and the degeneracy data [`CohCarrier.LevelLE`](def/CohCarrier_Level.html#L330) at indices $1$ and $q_k$ for $M\mid Mq_k\mid Mq_k^2$, (a) if $g,h\in H^1(\Gamma_0(M),A)$ (group homomorphisms $\Gamma_0(M)\to A$) satisfy $i_1(g)+i_{q_k}(h)=0$ then both $g$ and $h$ are Eisenstein for $T_{\ell_0}$, i.e. $T_{\ell_0}$ acts on them as $\ell_0+1$; and (b) if $x,z'\in H^1(\Gamma_0(Mq_k),A)$ satisfy $i_1(x)+i_{q_k}(z')=0$ then there is $w\in H^1(\Gamma_0(M),A)$ with $z'-i_1(w)$ and $x+i_{q_k}(w)$ Eisenstein for $T_{\ell_0}$. Let $r\in\mathbb N$, assume each weight-two level $N_k$ has an integral structure, and let $\theta_k\colon \mathbb T(N_k,2,S)\to\mathcal O/\mathfrak m$ be ring homomorphisms from the Hecke algebras such that for all primes $\ell\notin S$ with $\ell\nmid N_k$, every valuation subring $P$ of $\overline{\mathbb Q}$ over $\ell$ and every Frobenius $\sigma$ at $\ell$ for $P$, the characteristic polynomial of $\bar\rho(\sigma)$ is $X^2-\theta_k(T_\ell)X+\ell$. Let $\chi\colon\mathbb T(N_n,2,S)\to\mathcal O$ lift $\theta_n$, let $\pi_k$ be $\mathcal O$-algebra maps from the local Hecke algebra [`CuspForm.heckeLocal (Nf k) S 𝒪 (θf k)`](def/CuspForm_HeckeLocal.html#L131) to $\mathcal O$ agreeing with $\chi$ on the images of all $T_\ell$ with $\ell\notin S$, $\ell\nmid N_kN_n$ ($k\le n$), and let $a\colon\mathbb N\to\mathcal O$ be such that at each rung with $q_k\nmid N_{k+1}$ there is a rank-two adic Galois representation $\rho'$ over $\mathcal O$ with Frobenius characteristic polynomials $X^2-\pi_{k+1}(T_\ell)X+\ell$ for $\ell\notin S$, $\ell\nmid N_{k+1}$, unramified at $q_k$, with Frobenius trace $a_k$ at $q_k$. Then there exist types $M_k$, each an $\mathcal O$-module and a module over the local Hecke algebra at level $N_k$ compatibly, finite and free over $\mathcal O$, together with $\mathcal O$-bilinear forms $B_k$ on $M_k$, such that for $k\le n$: $B_k$ is Hecke-self-adjoint, $B_k$ is perfect (the induced map $M_k\to M_k^\ast$ is bijective), the submodule of $M_k$ annihilated by $\ker\pi_k$ is non-zero, and $\operatorname{rank}_{\mathcal O}M_k$ equals the rank of that submodule times $\operatorname{rank}_{\mathcal O}$ of the local Hecke algebra; for each $k<n$ there are $\mathcal O$-linear maps $i\colon M_{k+1}\to M_k$ and $j\colon M_k\to M_{k+1}$ adjoint for $B_{k+1},B_k$, and $\Delta$ in the local Hecke algebra at level $N_{k+1}$ with $j\circ i=\Delta\cdot$, such that $i$ carries the $\ker\pi_{k+1}$-torsion submodule onto the $\ker\pi_k$-torsion submodule, $\pi_{k+1}(\Delta)\neq 0$, and $\pi_{k+1}(\Delta)$ is divisible by $(q_k-1)(a_k^2-(q_k+1)^2)$ when $q_k\nmid N_{k+1}$ and by $q_k^2-1$ when $q_k\,\|\,N_{k+1}$; and finally, if $p\mid N_n$ forces $\bar\rho$ (viewed as an adic representation) to fail to be flat at $p$, then for some commutation datum `BaseOpComm` there is an $\mathcal O$-linear isomorphism of $M_n$ with [`CuspForm.AuxLevel.baseML (Nf n) r S 𝒪 (θf n)`](def/CuspForm_AuxLevelHeckeModuleBase.html#L31), the module attached to the Hecke data on $H^1(\Gamma_0(N_n),\mathcal O)$, carrying the action of each $T_\ell$ ($\ell$ prime, $\ell\notin S$, $\ell\nmid N_n$, $\ell\neq r$) to the action of the corresponding polynomial variable $X_g$ of the free algebra of that Hecke data.
--
--   This is the patching input of the Taylor–Wiles–Diamond level-raising argument: it produces, along a ladder of cube-free levels descending to the minimal level of $\bar\rho$, a compatible system of Hecke modules with perfect Hecke-self-adjoint pairings, with the expected multiplicativity of ranks, with rung maps whose composite is multiplication by an element of controlled $\pi$-value, and with the bottom module identified with the relevant localisation of $H^1(\Gamma_0(N_n),\mathcal O)$. It is the cube-free variant of the ladder construction, the extra hypothesis being that no prime $q\neq p$ divides a level to the third power, and it feeds the auxiliary-level version of the same statement used in the modularity lifting induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeLocal_exists_heckeModules_levelRaising_and_linearEquiv_baseML_of_isEis_kernel_pair_of_not_cube_dvd.lean

import Definitions.Def_CohCarrier_Tower
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_AuxLevelHeckeModuleBase
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.heckeLocal.exists_heckeModules_levelRaising_and_linearEquiv_baseML_of_isEis_kernel_pair_of_not_cube_dvd
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S Smin : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))

    (n : ℕ) (Nf : ℕ → ℕ) [∀ k, NeZero (Nf k)] (qf : ℕ → ℕ)
    (hNS : ∀ k, ∀ q : ℕ, q.Prime → q ∣ Nf k → q ∈ S)
    (hNp : ∀ k, k ≤ n → ¬ p ^ 2 ∣ Nf k ∧ (p ∣ Nf k ↔ p ∣ Nf n))
    (hNmin : ∀ k, k ≤ n → ∀ q ∈ Smin, q ≠ p → q ∣ Nf k)
    (hNunr : ∀ k, k ≤ n → ∀ q : ℕ, q.Prime → q ≠ p → q ∉ Smin → q ∣ Nf k → q ^ 2 ∣ Nf k)
    (hN3 : ∀ k, k ≤ n → ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ Nf k)
    (hfoot : Squarefree (Nf n) ∧ ∀ q : ℕ, q.Prime → q ≠ p → q ∣ Nf n → q ∈ Smin)
    (hrung : ∀ k, k < n → (qf k).Prime ∧ qf k ≠ p ∧ qf k ∈ S ∧
      ((¬ qf k ∣ Nf (k + 1) ∧ Nf k = Nf (k + 1) * qf k ^ 2) ∨
        (qf k ∣ Nf (k + 1) ∧ ¬ qf k ^ 2 ∣ Nf (k + 1) ∧ Nf k = Nf (k + 1) * qf k) ∨
        (qf k ^ 2 ∣ Nf (k + 1) ∧ Nf k = Nf (k + 1) * qf k)))

    (hihara : ∀ k, k < n → ¬ qf k ^ 2 ∣ Nf (k + 1) →
      ∀ (A : Type) [AddCommGroup A] [Module 𝒪 A] (ℓ₀ : ℕ) [NeZero ℓ₀] (M : ℕ) [NeZero (qf k)]
        (h₁ : CohCarrier.LevelLE M (M * qf k) ⊤ ⊤ 1)
        (hq : CohCarrier.LevelLE M (M * qf k) ⊤ ⊤ (qf k))
        (h₁' : CohCarrier.LevelLE (M * qf k) (M * qf k * qf k) ⊤ ⊤ 1)
        (hq' : CohCarrier.LevelLE (M * qf k) (M * qf k * qf k) ⊤ ⊤ (qf k)),
        ¬ qf k ∣ M → (∀ a : A, (qf k : ℤ) • a = 0 → a = 0) → ℓ₀.Prime → ¬ ℓ₀ ∣ M * qf k →
        (∀ g h : CohCarrier.H1 M ⊤ A,
            CohCarrier.iDeg' M (M * qf k) ⊤ ⊤ 1 A h₁ g +
                CohCarrier.iDeg' M (M * qf k) ⊤ ⊤ (qf k) A hq h = 0 →
              CohCarrier.IsEis 𝒪 A M ⊤ ℓ₀ g ∧ CohCarrier.IsEis 𝒪 A M ⊤ ℓ₀ h) ∧
        (∀ x z' : CohCarrier.H1 (M * qf k) ⊤ A,
            CohCarrier.iDeg' (M * qf k) (M * qf k * qf k) ⊤ ⊤ 1 A h₁' x +
                CohCarrier.iDeg' (M * qf k) (M * qf k * qf k) ⊤ ⊤ (qf k) A hq' z' = 0 →
              ∃ w : CohCarrier.H1 M ⊤ A,
                CohCarrier.IsEis 𝒪 A (M * qf k) ⊤ ℓ₀
                    (z' - CohCarrier.iDeg' M (M * qf k) ⊤ ⊤ 1 A h₁ w) ∧
                  CohCarrier.IsEis 𝒪 A (M * qf k) ⊤ ℓ₀
                    (x + CohCarrier.iDeg' M (M * qf k) ⊤ ⊤ (qf k) A hq w)))

    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)

    (r : ℕ)
    [∀ k, Fact (CuspForm.HasIntegralStructure (Nf k) 2)]

    (θf : ∀ k, CuspForm.heckeAlgebra (Nf k) 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ k (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ Nf k) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θf k (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (χ : CuspForm.heckeAlgebra (Nf n) 2 (↑S : Set ℕ) →+* 𝒪) (hχ : ∀ t, residue 𝒪 (χ t) = θf n t)
    (πT : ∀ k, CuspForm.heckeLocal (Nf k) (↑S : Set ℕ) 𝒪 (θf k) →ₐ[𝒪] 𝒪)
    (hπT : ∀ k, k ≤ n → ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ))
      (hℓk : ¬ ℓ ∣ Nf k) (hℓn : ¬ ℓ ∣ Nf n),
      πT k (CuspForm.heckeLocal.π (Nf k) (↑S : Set ℕ) 𝒪 (θf k) (CuspForm.heckeAlgebra.T hℓ hℓk hℓS)) =
        χ (CuspForm.heckeAlgebra.T hℓ hℓn hℓS))

    (a : ℕ → 𝒪)
    (ha : ∀ k, k < n → ¬ qf k ∣ Nf (k + 1) → ∃ ρ' : GaloisRepAdic 𝒪,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ Nf (k + 1)) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ'.ρ σ) =
              X ^ 2 - C (πT (k + 1) (CuspForm.heckeLocal.π (Nf (k + 1)) (↑S : Set ℕ) 𝒪 (θf (k + 1))
                (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) * X + C (ℓ : 𝒪)) ∧
      ρ'.IsUnramifiedAt (qf k) ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime (qf k) →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ (qf k) →
          LinearMap.trace 𝒪 _ (ρ'.ρ σ) = a k) :
    ∃ (M : ℕ → Type) (_ : ∀ k, AddCommGroup (M k))
      (_ : ∀ k, Module (CuspForm.heckeLocal (Nf k) (↑S : Set ℕ) 𝒪 (θf k)) (M k))
      (_ : ∀ k, Module 𝒪 (M k))
      (_ : ∀ k, IsScalarTower 𝒪 (CuspForm.heckeLocal (Nf k) (↑S : Set ℕ) 𝒪 (θf k)) (M k))
      (_ : ∀ k, Module.Finite 𝒪 (M k)) (_ : ∀ k, Module.Free 𝒪 (M k))
      (B : ∀ k, M k →ₗ[𝒪] M k →ₗ[𝒪] 𝒪),

    (∀ k, k ≤ n → ∀ (t : CuspForm.heckeLocal (Nf k) (↑S : Set ℕ) 𝒪 (θf k)) (m m' : M k),
      B k (t • m) m' = B k m (t • m')) ∧
    (∀ k, k ≤ n → Function.Bijective (B k)) ∧

    (∀ k, k ≤ n → Submodule.torsionBySet (CuspForm.heckeLocal (Nf k) (↑S : Set ℕ) 𝒪 (θf k)) (M k)
      ↑(RingHom.ker (πT k)) ≠ ⊥) ∧
    (∀ k, k ≤ n → Module.finrank 𝒪 (M k) =
      Module.finrank 𝒪 (Submodule.torsionBySet (CuspForm.heckeLocal (Nf k) (↑S : Set ℕ) 𝒪 (θf k))
        (M k) ↑(RingHom.ker (πT k))) *
        Module.finrank 𝒪 (CuspForm.heckeLocal (Nf k) (↑S : Set ℕ) 𝒪 (θf k))) ∧

    (∀ k, k < n →
      ∃ (i : M (k + 1) →ₗ[𝒪] M k) (j : M k →ₗ[𝒪] M (k + 1))
        (Δ : CuspForm.heckeLocal (Nf (k + 1)) (↑S : Set ℕ) 𝒪 (θf (k + 1))),
        (∀ (m' : M k) (m : M (k + 1)), B (k + 1) (j m') m = B k m' (i m)) ∧
        (∀ m : M (k + 1), j (i m) = Δ • m) ∧
        Submodule.map i ((Submodule.torsionBySet
            (CuspForm.heckeLocal (Nf (k + 1)) (↑S : Set ℕ) 𝒪 (θf (k + 1))) (M (k + 1))
            ↑(RingHom.ker (πT (k + 1)))).restrictScalars 𝒪) =
          (Submodule.torsionBySet (CuspForm.heckeLocal (Nf k) (↑S : Set ℕ) 𝒪 (θf k)) (M k)
            ↑(RingHom.ker (πT k))).restrictScalars 𝒪 ∧
        πT (k + 1) Δ ≠ 0 ∧
        (¬ qf k ∣ Nf (k + 1) → ((qf k : 𝒪) - 1) * (a k ^ 2 - ((qf k : 𝒪) + 1) ^ 2) ∣ πT (k + 1) Δ) ∧
        (qf k ∣ Nf (k + 1) → ¬ qf k ^ 2 ∣ Nf (k + 1) → ((qf k : 𝒪) ^ 2 - 1) ∣ πT (k + 1) Δ)) ∧

    ((p ∣ Nf n → ¬ (GaloisRepAdic.ofResidualGaloisRep ρbar).IsFlatAt p) →
      ∃ (hc₀ : CuspForm.AuxLevel.BaseOpComm (Nf n) r (↑S : Set ℕ) 𝒪)
        (e : M n ≃ₗ[𝒪] CuspForm.AuxLevel.baseML (Nf n) r (↑S : Set ℕ) 𝒪 (θf n) hc₀),
        ∀ (g : CuspForm.AuxLevel.Gen (Nf n) r (↑S : Set ℕ)) (m : M n),
          e (CuspForm.heckeLocal.π (Nf n) (↑S : Set ℕ) 𝒪 (θf n)
              (CuspForm.heckeAlgebra.T g.prime g.not_dvd g.notMem) • m) =
            (MvPolynomial.X g :
                (CuspForm.AuxLevel.baseHeckeData (Nf n) r (↑S : Set ℕ) 𝒪 (θf n) hc₀).FreeAlg) •
              e m) := by sorry
