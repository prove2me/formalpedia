-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime
-- name    : AutomorphicForm.exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/c7455017-c261-5286-9c12-b86db8b3c5b0
-- title:
--   Nonzero twisted cut trace carried by a fibre-constant cuspidal class
-- statement:
--   Let $K \subseteq L$ be number fields with $[L:K]$ prime, let $c_L,u_L,d_{1L},d_{2L}$ be reals with $d_{1L} < d_{2L}$, and let $T_L$ be a finite subset of $GL_2$ of the adeles of $L$ such that the union $\bigcup_{x \in T_L} (\,\cdot\, x)$-translates of `centreCutSiegelSet L cL uL d₁L d₂L` (the $g$ whose finite part is integral, whose archimedean components have local height at least $c_L$ and window coordinate at most $u_L^2$, and whose archimedean determinant norms lie in $[d_{1L},d_{2L}]$, at every infinite place) satisfies `CoversModCentre`: every $g$ can be moved into it by a global point on the left and a central idelic scalar on the right. Let $D$ be an idelic Galois descent datum for $L/K$ (a compatible continuous action of $\mathrm{Aut}_K(L)$ on the adele ring of $L$), $\sigma \neq 1$ an element of $L \simeq_{\mathrm{alg}[K]} L$, $S_K$ a finite set of primes of $\mathcal{O}_K$ and $S_L$ a finite set of primes of $\mathcal{O}_L$ containing every prime lying over $S_K$, $\xi_L$ a character of the full group of idele units of $L$, $N$ an ideal of $\mathcal{O}_L$, $\mathrm{tys}_L$ an archimedean type family for $L$, and $\varphi$ a continuous compactly supported complex function on $GL_2$ of the adeles of $L$ which is unit-factorizable above $K$ of type $\mathrm{tys}_L$ for the level subgroup `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` at $S_K$. Throughout, the carrier pins are `productionPinsOf` with the above covering set, those level subgroups, the Hecke generators `heckeGen`, full central subgroup, and the conditional measure on `adelicBox L`. Assume that for some Hecke eigensystem $\Psi$ over $L$ the $\sigma$-twisted cut trace `twistedCutTrace` of $\varphi$ on the isotypic cuspidal submodule attached to $(\xi_L, N, S_L, \Psi)$ intersected with the archimedean cut submodule for $\mathrm{tys}_L$ is nonzero. Then there exist a finite set $S_L'$ of primes of $\mathcal{O}_L$, an ideal $N_0$ and a Hecke eigensystem $\Psi'$ over $L$ such that: $S_L'$ consists exactly of the primes of $L$ lying over $S_K$; every prime dividing $N_0$ lies in $S_L'$; $\varphi$ is still unit-factorizable above $K$ of type $\mathrm{tys}_L$ for the level subgroup attached to $N_0$ at $S_K$; $\Psi'$ lies in `cuspClasses` for the same pins with $(\xi_L, N_0, S_L')$, i.e. $\Psi'$ has level $N_0$, its $a$- and $b$-data vanish on $S_L'$, and its isotypic cuspidal submodule is nonzero; $\Psi'$ agrees with $\Psi$ in $a$ and $b$ outside $S_L$; the pair $(\Psi'.a\,w, \Psi'.b\,w)$ depends only on the prime of $K$ below $w$, for $w \notin S_L'$; the value of $\xi_L$ on the determinant of `heckeGen` at $w$ likewise depends only on the prime of $K$ below $w$, for $w \notin S_L'$; and the $\sigma$-twisted cut trace of the same $\varphi$ for the data $(\xi_L, N_0, S_L', \Psi', \mathrm{tys}_L)$ is again nonzero.
--
--   This is a normalisation step in the twisted trace formula approach to cyclic base change for $GL_2$ in prime degree: a nonvanishing twisted cut trace is relocated onto a cuspidal class whose level and exceptional set are confined to the primes above a fixed finite set of primes of the base, and whose Hecke and central-character data are constant along the fibres of $\mathrm{Spec}\,\mathcal{O}_L \to \mathrm{Spec}\,\mathcal{O}_K$ outside that set. It is used in turn to produce such a class at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem
AutomorphicForm.exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (hdL : d₁L < d₂L)
    (hcovL : CoversModCentre L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : twistedCutTrace K L D σ
        (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc ≠ 0) :
    ∃ (SL' : Finset (HeightOneSpectrum (𝓞 L))) (N₀ : Ideal (𝓞 L)) (Ψ' : HeckeEigensystem L ℂ),
      (∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL' ↔ HeightOneSpectrum.under (𝓞 K) w ∈ SK) ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N₀ → w ∈ SL') ∧
      IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
      Ψ' ∈ cuspClasses L
        (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξL N₀ SL' ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → Ψ'.a w = Ψ.a w ∧ Ψ'.b w = Ψ.b w) ∧
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL' → w' ∉ SL' →
        HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
          (Ψ'.a w, Ψ'.b w) = (Ψ'.a w', Ψ'.b w')) ∧
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL' → w' ∉ SL' →
        HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
          ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ =
            ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩) ∧
      twistedCutTrace K L D σ
        (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξL N₀ SL' Ψ' tysL φ hφ hφc ≠ 0 := by sorry
