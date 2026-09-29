-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_symm
-- name    : AutomorphicForm.exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/a5a4fc69-f79e-5577-95f2-8596210fd149
-- title:
--   Cuspidal transfer of twisted cut trace, degree two or three
-- statement:
--   Let $K\subseteq L$ be number fields with $[L:K]=2$ or $3$. Fix reals $c_K,u_K,d_{1K},d_{2K}$ and a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$, and likewise $c_L,u_L,d_{1L},d_{2L}$, $T_L$ over $L$; assume $c_K>0$, $0<d_{1K}<d_{2K}$, $d_{1L}<d_{2L}$, and that over each of $K$ and $L$ the union $\bigcup_{x\in T}\,(\cdot\,x)$-translates of the centre-cut Siegel set (those $g$ whose finite part is integral, whose archimedean component at every infinite place has local height $\ge c$ and window square $\le u^2$, and whose archimedean determinant norm lies in $[d_1,d_2]$) covers $\mathrm{GL}_2(\mathbb{A})$ modulo global points and the adelic centre. Let $D$ be a continuous, $L$-compatible action of $L\simeq_{\mathrm{alg}[K]}L$ on the ring $\mathbb{A}_L$, and $\sigma\neq 1$ such an automorphism. Let $S_K$, $S_L$ be finite sets of primes such that every prime of $L$ over a prime in $S_K$ lies in $S_L$, and every prime of $L$ not over $S_K$ has ramification index $1$. Let $\xi_L$ be a character of $\mathbb{A}_L^\times$ (the group recorded by the carrier data over $L$, built from the above Siegel covering, the level family $N\mapsto U_1(N)$ intersected with the finite-adelic subgroup, the Hecke generators at finite places, and the adelic box, with Borel structures and Haar measures), $N$ an ideal of $\mathcal{O}_L$, $\mathrm{tys}_L$ an archimedean type family for $L$, and $\varphi$ a continuous compactly supported function on $\mathrm{GL}_2(\mathbb{A}_L)$ which is bi-invariant under $U_1(N)$ intersected with the finite-adelic subgroup, admits a semi-local factorisation over $S_K$ (archimedean factor, finite factor given by the product of semi-local factors at $v\in S_K$ on elements semi-locally integral outside $S_K$ and vanishing otherwise), and is archimedean bi-finite of type $\mathrm{tys}_L$. Let $\Psi$ be a Hecke eigensystem over $L$ with values in $\mathbb{C}$, and assume the $\sigma$-twisted cut trace of $\varphi$ — the trace of the twisted convolution operator attached to $D$ and $\sigma$ on the intersection of the $\Psi$-isotypic cusp submodule (for $\xi_L$, $N$, $S_L$) with the archimedean cut submodule of type $\mathrm{tys}_L$ — is non-zero. Let $N'\neq 0$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, $\mathrm{tys}_K$ an archimedean type family for $K$, and $f$ a function on $\mathrm{GL}_2(\mathbb{A}_K)$ that is unit-factorizable at $(\,\mathrm{principalLevel}(N')\cap$ finite-adelic subgroup$,\,S_K)$ and archimedean bi-finite of type $\mathrm{tys}_K$; assume $\varphi$ and $f$ are matching at $S_K$ with respect to $\sigma^{-1}$, that is, they admit factorisations as above whose archimedean factors match via $\sigma^{-1}$ and whose factors at each $v\in S_K$ match locally. Then there exist a character $\xi_K$ of $\mathbb{A}_K^\times$ (the group recorded by the corresponding carrier data over $K$, with the principal congruence level family) and a Hecke eigensystem $\pi$ over $K$ with $\pi$ in the cusp classes for $(\xi_K,N',S_K)$ — so $\pi$ has level $N'$, $\pi.a$ and $\pi.b$ vanish on $S_K$, and the $\pi$-isotypic cusp submodule is non-zero — such that for every prime $w$ of $L$ outside $S_L$ the formal base change of $\pi$ agrees with $\Psi$ at $w$: the Satake power of index the inertia degree of $w$ over the prime below, applied to $(\pi.a,\pi.b)$ at that prime, equals $\Psi.a\,w$, and $\pi.b$ at that prime raised to the inertia degree equals $\Psi.b\,w$.
--
--   This is the degree $2$ or $3$ instance of the twisted-trace comparison step: non-vanishing of a $\sigma$-twisted cut trace over $L$ at a function matching $f$ over $K$ produces a cuspidal class over $K$ of principal congruence level $N'$ whose formal base change has the Hecke parameters of $\Psi$ away from $S_L$. It feeds the existence statement for such a cuspidal class in degrees $2$ and $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_symm.lean

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

theorem AutomorphicForm.exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_symm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3)
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
    (hm : AreMatchingAt K L σ.symm SK φ f) :
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
