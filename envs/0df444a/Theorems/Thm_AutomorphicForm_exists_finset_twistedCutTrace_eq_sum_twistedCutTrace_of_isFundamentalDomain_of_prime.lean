-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime
-- name    : AutomorphicForm.exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/172cd332-280e-55d4-9a3c-7d74763b6a3f
-- title:
--   Nonzero twisted cut trace as a sum over fibre-constant cusp classes
-- statement:
--   Let $K \subseteq L$ be number fields with $[L:K]$ prime, let $0 < \alpha < \beta$ be reals, and let $\Phi_L$ be a subset of $\mathrm{GL}_2$ of the adeles of $L$ contained in the slab of those $g$ with $\|\det g\|_{\mathbb{A}_L} \in [\alpha,\beta]$ (idele norm via [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19)) and which is a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints` with respect to the adelic Haar measure on $\mathrm{GL}_2$ restricted to that slab. Let $D$ be an idele Galois descent datum for $L/K$ (a continuous action of $\mathrm{Gal}$-automorphisms on $\mathbb{A}_L$ by ring automorphisms compatible with $L \to \mathbb{A}_L$), $\sigma \neq 1$ an automorphism of $L$ over $K$, $S_K$ a finite set of finite places of $K$, and $S_L$ a finite set of finite places of $L$ containing every place lying over a place in $S_K$. Let $\xi_L$ be a character of the full group of ideles of $L$, $N$ an ideal of $\mathcal{O}_L$, $\mathrm{tys}_L$ an archimedean type family of $L$ (a finite list of archimedean representations at each infinite place), and $\varphi$ a continuous, compactly supported complex function on $\mathrm{GL}_2(\mathbb{A}_L)$ which is unit-factorizable above $K$ relative to $S_K$ and the level subgroup `levelOne` of $N$ intersected with the finite-adelic subgroup, and archimedean bi-finite of type $\mathrm{tys}_L$. Let $\Psi$ be a Hecke eigensystem for $L$ with complex coefficients, and assume the $\sigma$-twisted cut trace of right convolution by $\varphi$ on the isotypic cuspidal subspace attached to $(\xi_L, N, S_L, \Psi)$ intersected with the archimedean cut subspace is nonzero; here the carrier data are the production pins over $\Phi_L$ with level subgroups $M \mapsto \mathrm{levelOne}(M) \sqcap$ the finite-adelic subgroup, Hecke generators `heckeGen`, central subgroup $\top$, and the adelic measure conditioned on `adelicBox`. Then there exist a finite set $S_L'$ of finite places of $L$, an ideal $N_0$ of $\mathcal{O}_L$ and a finite set $C$ of Hecke eigensystems for $L$ such that: $S_L'$ consists exactly of the places of $L$ lying over places in $S_K$; every prime dividing $N_0$ lies in $S_L'$; $\varphi$ is still unit-factorizable above $K$ of type $\mathrm{tys}_L$ for the level subgroup of $N_0$ and $S_K$; each $\Psi' \in C$ lies in the cusp classes for the same pins and $\xi_L$ at level $N_0$ and exceptional set $S_L'$ (that is, $\Psi'$ has level $N_0$, its eigenvalues $a$ and $b$ vanish at all places of $S_L'$, and the corresponding isotypic cuspidal subspace is nonzero), agrees with $\Psi$ in both $a$ and $b$ at every place outside $S_L$, and has $(\Psi'.a(w), \Psi'.b(w))$ depending only on the place of $K$ below $w$ for $w \notin S_L'$; and the original twisted cut trace at $(N, S_L, \Psi)$ equals the sum over $\Psi' \in C$ of the twisted cut traces at $(N_0, S_L', \Psi')$, with the same $\varphi$ and type family.
--
--   This is the spectral bookkeeping step that replaces a single nonzero twisted cut trace by a finite sum of twisted cut traces over cuspidal classes whose level and exceptional set are adapted to the set $S_K$ of places of $K$ and whose Hecke data are constant along the fibres over $K$, as in the base change argument for $\mathrm{GL}(2)$ over a cyclic extension of prime degree. It is used to produce a single class with nonvanishing twisted cut trace in [`AutomorphicForm.exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime`](thm.html#AutomorphicForm.exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
AutomorphicForm.exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : twistedCutTrace K L D σ
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc ≠ 0) :
    ∃ (SL' : Finset (HeightOneSpectrum (𝓞 L))) (N₀ : Ideal (𝓞 L)) (C : Finset (HeckeEigensystem L ℂ)),
      (∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL' ↔ HeightOneSpectrum.under (𝓞 K) w ∈ SK) ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N₀ → w ∈ SL') ∧
      IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
      (∀ Ψ' ∈ C,
        Ψ' ∈ cuspClasses L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N₀ SL' ∧
        (∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → Ψ'.a w = Ψ.a w ∧ Ψ'.b w = Ψ.b w) ∧
        (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL' → w' ∉ SL' →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
            (Ψ'.a w, Ψ'.b w) = (Ψ'.a w', Ψ'.b w'))) ∧
      twistedCutTrace K L D σ
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc =
        ∑ Ψ' ∈ C, twistedCutTrace K L D σ
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N₀ SL' Ψ' tysL φ hφ hφc := by sorry
