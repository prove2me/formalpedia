-- Prove2me | Theorems.Thm_CuspForm_HeckeGaloisRepDatum_exists_algHom_comp_eq_and_linearEquiv_semilinear_auxLevel_ML
-- name    : CuspForm.HeckeGaloisRepDatum.exists_algHom_comp_eq_and_linearEquiv_semilinear_auxLevel_ML
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/9b8ff4a0-47bd-596b-90f8-e8cb50e1ed8f
-- title:
--   Normalising a Hecke–Galois datum by a twist τ of T
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring of characteristic zero with finite residue field $k$, and let $p\neq 2$ be a prime lying in its maximal ideal. Let $\bar\rho$ be a two-dimensional residual representation over $k$ (factoring through a finite extension of $\mathbb Q$), absolutely irreducible after base change to $\overline{k}$. Finite sets $S\supseteq S_{\min}\ni p$ of primes, a nonzero squarefree level $N$, and an auxiliary prime $r\ge 5$ are subject to the usual minimality, tameness, divisibility and Frobenius-trace conditions ($q\in S_{\min}$ iff $\bar\rho$ is ramified at $q$ for $q\neq p$; inertia unipotent at such $q$; $p\mid N$ only if $\bar\rho$ is not flat at $p$; $r\notin S$, $r\nmid Np$, $p\nmid r-1$, $(\operatorname{tr}\bar\rho(\mathrm{Frob}_r))^2\neq(r+1)^2$), summarised here, together with the assumption that weight-two cusp forms of level $N$ are spanned by their integral $q$-expansion lattice. Given a character $\theta$ of the Hecke algebra $\mathbb T=$[`CuspForm.heckeAlgebra N 2 S`](def/CuspForm_HeckeAlgebra.html#L18) into $k$ whose $T_\ell$-values give the Frobenius characteristic polynomials $X^2-\theta(T_\ell)X+\ell$ of $\bar\rho$ at primes $\ell\nmid N$, $\ell\notin S$, put $T=$[`CuspForm.heckeLocal N S 𝒪 θ`](def/CuspForm_HeckeLocal.html#L131) with its canonical structure map $\pi_0$. Let `Hn` be any Hecke–Galois datum on $T$ (a map $\pi:\mathbb T\to T$ reducing to $\theta$ whose image generates $T$ over $\mathcal O$, interpolating $\mathcal O$-valued characters lifting $\theta$, together with a rank-two $T$-representation with Frobenius charpolys $X^2-\pi(T_\ell)X+\ell$ and absolutely irreducible residual representation). Let $L$ be a $T$-module, finite and free over $\mathcal O$ with compatible scalars, together with an $\mathcal O$-linear isomorphism of $L$ onto the auxiliary-level module [`CuspForm.AuxLevel.ML N r S 𝒪 θ hc`](def/CuspForm_AuxLevelHeckeModule.html#L46) built from commuting Hecke operators at level $Nr$, carrying the action of $\pi_0(T_\ell)$ on $L$ to the action of the polynomial variable $X_g$ for each generator $g$ (a prime $\ell\notin S$ with $\ell\nmid N$, $\ell\neq r$). Finally let $\mathcal D$ be a deformation condition, `Dmin` a universal deformation datum for $\bar\rho$ of type $\mathcal D$ with ring $R$ and representation $\rho_R$, and $\varphi:R\to T$ a local $\mathcal O$-algebra map with $\rho_R\otimes_{\varphi}T$ equivalent to the representation of `Hn`. The conclusion: there exist an $\mathcal O$-algebra endomorphism $\tau$ of $T$ and a local $\mathcal O$-algebra map $\varphi_0:R\to T$ with $\varphi=\tau\circ\varphi_0$, such that the base change of $\rho_R$ along $\varphi_0$ has Frobenius characteristic polynomial $X^2-\pi_0(T_\ell)X+\ell$ at every prime $\ell\nmid N$, $\ell\notin S$ (for every valuation subring of $\overline{\mathbb Q}$ over $\ell$ and every Frobenius element there), and there exists an $\mathcal O$-linear automorphism $\Theta$ of $L$ which is $\tau$-semilinear: $\Theta(x\cdot m)=\tau(x)\cdot\Theta(m)$ for all $x\in T$, $m\in L$.
--
--   This is the normalisation step of the Taylor–Wiles patching argument: an arbitrary Hecke–Galois datum on the localised Hecke algebra $T$ is replaced by one whose Frobenius traces are given by the canonical structure map $\pi_0$, at the cost of composing the map from the deformation ring with an endomorphism $\tau$ of $T$ and transporting the Hecke module $L$ along a $\tau$-semilinear automorphism. It is used by the constructions of Taylor–Wiles modules at auxiliary level, in both the flat and the non-flat (ordinary) cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_HeckeGaloisRepDatum_exists_algHom_comp_eq_and_linearEquiv_semilinear_auxLevel_ML.lean

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_AuxLevelHeckeModule
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.HeckeGaloisRepDatum.exists_algHom_comp_eq_and_linearEquiv_semilinear_auxLevel_ML
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S Smin : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)

    (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (hNmin : ∀ q ∈ Smin, q ≠ p → q ∣ N)
    (hN : Squarefree N ∧ ∀ q : ℕ, q.Prime → q ≠ p → q ∣ N → q ∈ Smin)
    (hguard : p ∣ N → ¬ (GaloisRepAdic.ofResidualGaloisRep ρbar).IsFlatAt p)

    (r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r) (hrS : r ∉ S) (hrN : ¬ r ∣ N * p) (hr1 : ¬ p ∣ r - 1)
    (hrρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
        LinearMap.trace (ResidueField 𝒪) ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : ResidueField 𝒪) + 1) ^ 2)
    [Fact (CuspForm.HasIntegralStructure N 2)]

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (Hn : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ))

    (L : Type) [AddCommGroup L] [Module (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) L] [Module 𝒪 L]
    [IsScalarTower 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) L] [Module.Finite 𝒪 L] [Module.Free 𝒪 L]
    (hc : CuspForm.AuxLevel.OpComm N r (↑S : Set ℕ) 𝒪)
    (eML : L ≃ₗ[𝒪] CuspForm.AuxLevel.ML N r (↑S : Set ℕ) 𝒪 θ hc)
    (heML : ∀ (g : CuspForm.AuxLevel.Gen N r (↑S : Set ℕ)) (m : L),
      eML (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T g.prime g.not_dvd g.notMem) • m) =
        (MvPolynomial.X g : (CuspForm.AuxLevel.heckeData N r (↑S : Set ℕ) 𝒪 θ hc).FreeAlg) • eML m)

    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (Dmin : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    (φ : Dmin.R →ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ)
    (hφ : IsLocalHom (φ : Dmin.R →+* CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ))
    (hequiv : (Dmin.ρ.baseChangeAlong (φ : Dmin.R →+* _) hφ).IsEquiv Hn.ρ) :
    ∃ (τ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ)
      (φ₀ : Dmin.R →ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ)
      (hφ₀ : IsLocalHom (φ₀ : Dmin.R →+* CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ)),
      (∀ x : Dmin.R, φ x = τ (φ₀ x)) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly ((Dmin.ρ.baseChangeAlong
                (φ₀ : Dmin.R →+* CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) hφ₀).ρ σ) =
              X ^ 2 - C (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X +
                C (ℓ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ)) ∧
      ∃ Θ : L ≃ₗ[𝒪] L, ∀ (x : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) (m : L), Θ (x • m) = τ x • Θ m := by sorry
