-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime
-- name    : AutomorphicForm.exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/3b1484b2-620b-55f4-96e1-616ed4402777
-- title:
--   Cyclic prime-degree base change from a non-vanishing twisted cut trace
-- statement:
--   Let $K\subseteq L$ be number fields with $[L:K]$ prime. Over $K$ fix reals $c_K,u_K,d_{1K},d_{2K}$ with $c_K>0$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb A_K)$ such that the union of the right translates $(\cdot\,x)$ of the centre-cut Siegel set (finite part integral, local height at least $c_K$ at every infinite place, window $x$-coordinate squared at most $u_K^2$, archimedean determinant norms in $[d_{1K},d_{2K}]$) covers $\mathrm{GL}_2(\mathbb A_K)$ modulo global points and central ideles; likewise $c_L,u_L,d_{1L}<d_{2L}$ and $T_L$ over $L$. Let $D$ be an idelic Galois descent datum for $L/K$ (a continuous action of $\mathrm{Gal}$ on $\mathbb A_L$ compatible with $L$) and $\sigma\neq 1$ in $L\simeq_K L$. Let $S_K$, $S_L$ be finite sets of finite places with every place of $L$ above $S_K$ lying in $S_L$, and with $e(w\mid w\cap K)=1$ for every $w$ not above $S_K$. Let $\xi_L$ be a character of the full idele unit group of $L$, $N$ an ideal of $\mathcal O_L$, $\mathrm{tys}_L$ an archimedean type family, and $\varphi$ a continuous compactly supported function on $\mathrm{GL}_2(\mathbb A_L)$ which is bi-invariant under $U_1(N)$ intersected with the kernel of the archimedean projection, admits a semi-local factorization relative to $S_K$ (archimedean factor, finite factor, semi-local factors at places of $S_K$, the product formula away from $S_K$ and vanishing off the semi-local integral sets), and is archimedeanly bi-finite for $\mathrm{tys}_L$. Let $\Psi$ be a Hecke eigensystem over $L$ with complex values and assume that the twisted cut trace — the trace of the $D,\sigma$-twisted convolution by $\varphi$ on the intersection of the $\Psi$-isotypic cusp submodule at level $N$ away from $S_L$ with central character $\xi_L$ and the archimedean cut submodule for $\mathrm{tys}_L$, for the carrier data given by the Siegel union over $L$, the level family $U_1(\cdot)$, the Hecke generators $\mathrm{heckeGen}$ and the adelic box — is non-zero. Finally let $N'\neq 0$ be an ideal of $\mathcal O_K$ all of whose prime divisors lie in $S_K$, $\mathrm{tys}_K$ an archimedean type family over $K$, and $f$ a function on $\mathrm{GL}_2(\mathbb A_K)$ that is unit-factorizable of type $\mathrm{tys}_K$ at the principal level $N'$ intersected with the kernel of the archimedean projection relative to $S_K$, and assume $\varphi$ and $f$ match at $\sigma^{-1}$ over $S_K$ (matching factorizations, archimedean matching and local matching at each $v\in S_K$). Then there are a character $\xi_K$ of the full idele unit group of $K$ and a Hecke eigensystem $\pi$ over $K$ lying in the cusp classes for the analogous carrier data over $K$ with the principal level family, at $\xi_K$, $N'$, $S_K$ (that is, $\pi$ has level $N'$, $\pi.a$ and $\pi.b$ vanish on $S_K$, and the corresponding isotypic cusp submodule is non-zero), such that for every place $w$ of $L$ outside $S_L$ the formal base change of $\pi$ agrees with $\Psi$ at $w$: the Satake power of index the inertia degree $f(w\mid w\cap K)$ of $(\pi.a,\pi.b)$ at $w\cap K$ equals $\Psi.a(w)$, and $\pi.b(w\cap K)^{f(w\mid w\cap K)}=\Psi.b(w)$.
--
--   This is the extraction of cyclic base change for cuspidal data of $\mathrm{GL}_2$ in prime degree from the comparison of the $\sigma$-twisted trace over $L$ with the trace over $K$: non-vanishing of a twisted cut trace against a matching pair of test functions produces a cuspidal Hecke eigensystem over $K$ at a principal congruence level whose formal base change matches the given eigensystem over $L$ outside the bad set. It feeds the companion statement phrased with the matching at $\sigma$ rather than $\sigma^{-1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (hdL : d₁L < d₂L)
    (hcovL : CoversModCentre L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ξL : (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : twistedCutTrace K L D σ
      (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc ≠ 0)
    (N' : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hN'₀ : N' ≠ ⊥) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (hft : IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) SK f)
    (hm : AreMatchingAt K L σ⁻¹ SK φ f) :
    ∃ (ξK : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
      (π : HeckeEigensystem K ℂ),
      π ∈ cuspClasses K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K))
        ξK N' SK ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
        (formalBaseChange K L π).a w = Ψ.a w ∧ (formalBaseChange K L π).b w = Ψ.b w) := by sorry
