-- Prove2me | Theorems.Thm_AutomorphicForm_exists_twistedCutTrace_ne_zero_of_pos_of_isArithGenuineCuspRealizable_of_isConstantOnFibers
-- name    : AutomorphicForm.exists_twistedCutTrace_ne_zero_of_pos_of_isArithGenuineCuspRealizable_of_isConstantOnFibers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/b59d3157-33c4-5268-b12a-0873c0dd667b
-- title:
--   Non-vanishing twisted cut trace for a fibre-constant eigensystem
-- statement:
--   Let $K \subseteq L$ be number fields, let $c_L,u_L,d_{1,L},d_{2,L}$ be reals with $d_{1,L}<d_{2,L}$, $0<c_L$ and $0<d_{1,L}$, and let $T_L$ be a finite set of points of $GL_2$ over the adèles of $L$. Assume the union $\bigcup_{x\in T_L}(\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\,]$ of right translates of the centre-cut Siegel window (finite component integral; local height $\ge c_L$, window $\mathrm{xWindowSq}\le u_L^2$ and archimedean determinant norm in $[d_{1,L},d_{2,L}]$ at every infinite place) covers $GL_2$ of the adèles modulo $GL_2(L)$ on the left and central idèles on the right. Let $D$ be an idèle Galois descent datum for $L/K$ (a homomorphism from $L\simeq_K L$ to continuous ring automorphisms of the adèle ring compatible with $L$), $\sigma : L\simeq_K L$, and let $\Phi_L$ be a complex Hecke eigensystem over $L$ (level $\ne \bot$, Satake data $a,b$ on the primes) which is arithmetically genuinely cusp-realizable for the production pins attached to that covering set, with levels $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}$ and probability measure conditioned on the adelic box, and which is constant on fibres over $K$: outside a finite set of primes of $L$, $a$ and $b$ agree at primes with the same prime of $K$ below and the same inertia degree. Then there are a character $\xi_L$ of the pins' centre, an ideal $N$ of $\mathcal{O}_L$, finite sets $S_K$ of primes of $K$ and $S_L$ of primes of $L$, an archimedean type family $\mathrm{tys}_L$ over $L$, a continuous compactly supported $\varphi$ on $GL_2$ of the adèles of $L$, and a Hecke eigensystem $\Psi$ over $L$ such that: every prime of $L$ lying over $S_K$ lies in $S_L$; every prime of $L$ whose prime below is outside $S_K$ has ramification index $1$; $\varphi$ is unit-factorizable above $S_K$ for the level group $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$ and archimedean-bi-finite of type $\mathrm{tys}_L$; $\Psi$ lies in the cusp classes for these pins, $\xi_L$, $N$, $S_L$, i.e. $\Psi$ has level $N$, vanishing Satake data at the primes of $S_L$ and nonzero isotypic cusp submodule; $\Psi$ has the same $a$ and $b$ as $\Phi_L$ at all primes outside $S_L$; and the twisted cut trace of $\varphi$ — the $\sigma$-twisted convolution trace, via $D$, on the intersection of that isotypic cusp submodule with the archimedean cut submodule of type $\mathrm{tys}_L$ — is nonzero.
--
--   This is the non-vanishing of a twisted trace in the base-change argument for $GL_2$: an eigensystem over $L$ whose Satake data are constant on the fibres of $L/K$ is matched, outside a finite set of primes, by a cuspidal class carrying a nonzero $\sigma$-twisted trace on a finite-dimensional space of vectors of fixed level and fixed archimedean types. It feeds the construction of a formal base change, being cited by [`AutomorphicForm.exists_formalBaseChange_of_isConstantOnFibers_of_finrank_two_or_three_of_coversModCentre`](thm.html#AutomorphicForm.exists_formalBaseChange_of_isConstantOnFibers_of_finrank_two_or_three_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_twistedCutTrace_ne_zero_of_pos_of_isArithGenuineCuspRealizable_of_isConstantOnFibers.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.exists_twistedCutTrace_ne_zero_of_pos_of_isArithGenuineCuspRealizable_of_isConstantOnFibers
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (hdL : d₁L < d₂L)
    (hcL : 0 < cL) (hd₁L : 0 < d₁L)
    (hcovL : CoversModCentre L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ΦL : HeckeEigensystem L ℂ)
    (hΦL : IsArithGenuineCuspRealizable L
      (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)) ΦL)
    (hinv : ΦL.IsConstantOnFibers K) :
    ∃ (ξL : (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
      (N : Ideal (𝓞 L)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
      (tysL : ArchTypeFamily L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
      (Ψ : HeckeEigensystem L ℂ),
      (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL) ∧
      (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) ∧
      IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
      Ψ ∈ cuspClasses L
        (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξL N SL ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → Ψ.a w = ΦL.a w ∧ Ψ.b w = ΦL.b w) ∧
      twistedCutTrace K L D σ
        (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc ≠ 0 := by sorry
