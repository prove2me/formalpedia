-- Prove2me | Theorems.Thm_CuspForm_heckeLocal_exists_isCornerRealization_and_rung_of_isCornerRealization_of_dvd_of_not_sq_dvd_of_not_cube_dvd
-- name    : CuspForm.heckeLocal.exists_isCornerRealization_and_rung_of_isCornerRealization_of_dvd_of_not_sq_dvd_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/f713939f-9208-58ba-83cb-9d257eb62ce5
-- title:
--   Level raising at q ∣ N for Hecke corner realisations
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring of characteristic zero with finite residue field $k=\mathrm{ResidueField}\,\mathcal O$, and let $p$ be an odd prime with $p\in\mathfrak m_{\mathcal O}$. Let $\bar\rho$ be a two-dimensional residual Galois representation over $k$ (a monoid homomorphism from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_k(V)$, $\dim V=2$, trivial on some finite level) which is absolutely irreducible, and let $S\supseteq S_{\min}$ be finite sets of naturals with all members of $S$ prime and $p\in S_{\min}$, such that a prime $q'\neq p$ lies in $S_{\min}$ exactly when $\bar\rho$ is ramified at $q'$, and such that for $q'\in S_{\min}$, $q'\neq p$, inertia at $q'$ has characteristic polynomial $(X-1)^2$ in $\bar\rho$. Let $q\in S$ be a prime, $q\neq p$, and let $N,N',L,L'$ be nonzero with $N'=Nq$, $L'=Lq$, $q\mid N$, $q^2\nmid N$, every prime divisor of $N$ in $S$, $p^2\nmid N$, every $q'\in S_{\min}\setminus\{p\}$ dividing $N$, every prime $q'\neq p$ dividing $N$ but outside $S_{\min}$ having $q'^2\mid N$, no prime $q'\neq p$ with $q'^3\mid N$, and $L\mid N$ with the same prime divisors as $N$, with $q'^2\mid N\Rightarrow q'^2\mid L$ and $L$ cube-free; weight-two cusp forms of levels $N$ and $N'$ are assumed spanned by forms with integral $q$-expansions. Let $\theta$ (resp. $\theta'$) be a ring homomorphism from the anemic Hecke algebra $\mathbb T^S(N)$ (resp. $\mathbb T^S(N')$) of weight two, generated over $\mathbb Z$ by the $T_\ell$ with $\ell$ prime, $\ell\nmid N$ (resp. $\ell \nmid N'$), $\ell\notin S$ and the $U_{q'}$ with $q'\mid N$ (resp. $q' \mid N'$), $q'\notin S$, into $k$, such that for all such $\ell$ and every Frobenius element $\sigma$ at $\ell$ relative to a valuation subring of $\overline{\mathbb Q}$ over $\ell$ one has $\mathrm{charpoly}(\bar\rho(\sigma))=X^2-\theta(T_\ell)X+\ell$ (resp. with $\theta'$). Let $\pi_T$, $\pi_{T'}$ be $\mathcal O$-algebra maps to $\mathcal O$ from the localisations $\mathbb T^S(N)_\theta$, $\mathbb T^S(N')_{\theta'}$, agreeing on the images of the $T_\ell$ for $\ell\notin S$ prime with $\ell\nmid N'$. Assume the following Ihara-type input: for every $\mathcal O$-module $A$ on which multiplication by $q$ is injective, every prime $\ell_0$ and every level $M_0$ with $q\nmid M_0$, $\ell_0\nmid M_0q$, and degeneracy data ([`CohCarrier.LevelLE`](def/CohCarrier_Level.html#L330)) for the maps $1$ and $q$ from $M_0$ to $M_0q$ and from $M_0q$ to $M_0q^2$, (i) if $g,h\in H^1(M_0,A)$ satisfy $i_1g+i_qh=0$ then both $g$ and $h$ are Eisenstein at $\ell_0$ (that is, $T_{\ell_0}$ acts as $\ell_0+1$), and (ii) if $x,z'\in H^1(M_0q,A)$ satisfy $i_1x+i_qz'=0$ then there is $w\in H^1(M_0,A)$ with $z'-i_1w$ and $x+i_qw$ Eisenstein at $\ell_0$. Finally let $M$ be a finite free $\mathcal O$-module which is also a $\mathbb T^S(N)_\theta$-module compatibly with its $\mathcal O$-structure, and $B\colon M\times M\to\mathcal O$ an $\mathcal O$-bilinear form, such that [`CuspForm.heckeLocal.IsCornerRealization`](def/CuspForm_HeckeModuleCornerRealization.html#L19) holds for $p,\bar\rho,N,L,S,\theta,M,B$: there are a commuting family of Hecke operators on $H^1(L,\mathcal O)$ indexed by the generators $\mathrm{Gen}(L,S)$, an eigensystem $\bar\theta$ on these generators with $\bar\theta(T_\ell)=\theta(T_\ell)$, $\bar\theta(U_{q'})=0$ when $q'^2\mid L$ and $\bar\theta(U_p)\neq0$ if $\bar\rho$ is ordinary at $p$, an idempotent splitting of the generated subalgebra with a chosen index $i_0$ and a point $\pi_k$ of the corner ring inducing $\bar\theta$, such that the corner $e_{i_0}H^1(L,\mathcal O)$ consists of parabolic homomorphisms and an $\mathcal O$-isomorphism of $M$ with that corner intertwines the action of $T_\ell$ with the cohomological Hecke operator and carries $B$ to the pairing [`CuspForm.Bfam₀`](def/CuspForm_CornerPairingFamily.html#L140). Then there exist a finite free $\mathcal O$-module $M'$ carrying a compatible $\mathbb T^S(N')_{\theta'}$-action and an $\mathcal O$-bilinear form $B'$ such that `IsCornerRealization` holds for $p,\bar\rho,N',L',S,\theta',M',B'$, together with $\mathcal O$-linear maps $i\colon M\to M'$ and $j\colon M'\to M$ and an element $\Delta\in\mathbb T^S(N)_\theta$ satisfying: $B(j\,m')(m)=B'(m')(i\,m)$ for all $m'\in M'$, $m\in M$; $j(i\,m)=\Delta\cdot m$ for all $m$; $i$ maps the submodule of $M$ annihilated by $\ker\pi_T$ onto the submodule of $M'$ annihilated by $\ker\pi_{T'}$; $\pi_T(\Delta)\neq0$; and $(q^2-1)\mid\pi_T(\Delta)$ in $\mathcal O$.
--
--   This is one rung of the level-raising induction at a prime $q$ exactly dividing $N$: it transports a corner realisation of a Hecke module at level $N$ (with auxiliary cube-free level $L$) to one at level $Nq$ (with level $Lq$), together with an adjoint pair of degeneracy maps whose composite acts by an element of the localised Hecke algebra whose image under $\pi_T$ is nonzero and divisible by $q^2-1$, and with the $\pi_T$-eigenspaces matching exactly. It is the cube-free-level form of the step, and is used in the construction of the level-raised Hecke modules and the comparison of the resulting base modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeLocal_exists_isCornerRealization_and_rung_of_isCornerRealization_of_dvd_of_not_sq_dvd_of_not_cube_dvd.lean

import Definitions.Def_CohCarrier_Tower
import Definitions.Def_CuspForm_HeckeModuleCornerRealization
import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.heckeLocal.exists_isCornerRealization_and_rung_of_isCornerRealization_of_dvd_of_not_sq_dvd_of_not_cube_dvd
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S Smin : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)

    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) (hqS : q ∈ S)
    (N N' L L' : ℕ) [NeZero N] [NeZero N'] [NeZero L] [NeZero L'] [NeZero q]
    (hN' : N' = N * q) (hL' : L' = L * q) (hqN : q ∣ N) (hqN2 : ¬ q ^ 2 ∣ N)
    (hNS : ∀ q' : ℕ, q'.Prime → q' ∣ N → q' ∈ S)
    (hNp : ¬ p ^ 2 ∣ N)
    (hNmin : ∀ q' ∈ Smin, q' ≠ p → q' ∣ N)
    (hNunr : ∀ q' : ℕ, q'.Prime → q' ≠ p → q' ∉ Smin → q' ∣ N → q' ^ 2 ∣ N)
    (hN3 : ∀ q' : ℕ, q'.Prime → q' ≠ p → ¬ q' ^ 3 ∣ N)
    (hLN : L ∣ N) (hNL : ∀ q' : ℕ, q'.Prime → q' ∣ N → q' ∣ L)
    (hNL2 : ∀ q' : ℕ, q'.Prime → q' ^ 2 ∣ N → q' ^ 2 ∣ L) (hL3 : ∀ q' : ℕ, q'.Prime → ¬ q' ^ 3 ∣ L)
    [Fact (CuspForm.HasIntegralStructure N 2)] [Fact (CuspForm.HasIntegralStructure N' 2)]

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    (θ' : CuspForm.heckeAlgebra N' 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N') (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ' (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (πT : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] 𝒪)
    (πT' : CuspForm.heckeLocal N' (↑S : Set ℕ) 𝒪 θ' →ₐ[𝒪] 𝒪)
    (hπ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN' : ¬ ℓ ∣ N') (hℓN : ¬ ℓ ∣ N),
      πT' (CuspForm.heckeLocal.π N' (↑S : Set ℕ) 𝒪 θ' (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS)) =
        πT (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)))

    (hihara : ∀ (A : Type) [AddCommGroup A] [Module 𝒪 A] (ℓ₀ : ℕ) [NeZero ℓ₀] (M₀ : ℕ)
        (h₁ : CohCarrier.LevelLE M₀ (M₀ * q) ⊤ ⊤ 1)
        (hq₁ : CohCarrier.LevelLE M₀ (M₀ * q) ⊤ ⊤ q)
        (h₁' : CohCarrier.LevelLE (M₀ * q) (M₀ * q * q) ⊤ ⊤ 1)
        (hq' : CohCarrier.LevelLE (M₀ * q) (M₀ * q * q) ⊤ ⊤ q),
        ¬ q ∣ M₀ → (∀ x : A, (q : ℤ) • x = 0 → x = 0) → ℓ₀.Prime → ¬ ℓ₀ ∣ M₀ * q →
        (∀ g h : CohCarrier.H1 M₀ ⊤ A,
            CohCarrier.iDeg' M₀ (M₀ * q) ⊤ ⊤ 1 A h₁ g +
                CohCarrier.iDeg' M₀ (M₀ * q) ⊤ ⊤ q A hq₁ h = 0 →
              CohCarrier.IsEis 𝒪 A M₀ ⊤ ℓ₀ g ∧ CohCarrier.IsEis 𝒪 A M₀ ⊤ ℓ₀ h) ∧
        (∀ x z' : CohCarrier.H1 (M₀ * q) ⊤ A,
            CohCarrier.iDeg' (M₀ * q) (M₀ * q * q) ⊤ ⊤ 1 A h₁' x +
                CohCarrier.iDeg' (M₀ * q) (M₀ * q * q) ⊤ ⊤ q A hq' z' = 0 →
              ∃ w : CohCarrier.H1 M₀ ⊤ A,
                CohCarrier.IsEis 𝒪 A (M₀ * q) ⊤ ℓ₀
                    (z' - CohCarrier.iDeg' M₀ (M₀ * q) ⊤ ⊤ 1 A h₁ w) ∧
                  CohCarrier.IsEis 𝒪 A (M₀ * q) ⊤ ℓ₀
                    (x + CohCarrier.iDeg' M₀ (M₀ * q) ⊤ ⊤ q A hq₁ w)))

    (M : Type) [AddCommGroup M] [Module (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M] [Module 𝒪 M]
    [IsScalarTower 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪)
    (hM : CuspForm.heckeLocal.IsCornerRealization p ρbar N L (↑S : Set ℕ) θ M B) :
    ∃ (M' : Type) (_ : AddCommGroup M')
      (_ : Module (CuspForm.heckeLocal N' (↑S : Set ℕ) 𝒪 θ') M') (_ : Module 𝒪 M')
      (_ : IsScalarTower 𝒪 (CuspForm.heckeLocal N' (↑S : Set ℕ) 𝒪 θ') M')
      (_ : Module.Finite 𝒪 M') (_ : Module.Free 𝒪 M')
      (B' : M' →ₗ[𝒪] M' →ₗ[𝒪] 𝒪),
      CuspForm.heckeLocal.IsCornerRealization p ρbar N' L' (↑S : Set ℕ) θ' M' B' ∧
      ∃ (i : M →ₗ[𝒪] M') (j : M' →ₗ[𝒪] M) (Δ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ),
        (∀ (m' : M') (m : M), B (j m') m = B' m' (i m)) ∧
        (∀ m : M, j (i m) = Δ • m) ∧
        Submodule.map i ((Submodule.torsionBySet (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M
            ↑(RingHom.ker πT)).restrictScalars 𝒪) =
          (Submodule.torsionBySet (CuspForm.heckeLocal N' (↑S : Set ℕ) 𝒪 θ') M'
            ↑(RingHom.ker πT')).restrictScalars 𝒪 ∧
        πT Δ ≠ 0 ∧
        ((q : 𝒪) ^ 2 - 1) ∣ πT Δ := by sorry
