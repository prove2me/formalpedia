-- Prove2me | Theorems.Thm_AutomorphicForm_sigmaSectionActOn_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional
-- name    : AutomorphicForm.sigmaSectionActOn_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/3c5722f9-e9a2-5635-88af-63aa6f91dfdb
-- title:
--   Galois twist stabilises a finite-dimensional isotypic cusp space
-- statement:
--   Let $K\subseteq L$ be number fields, let $\sigma$ be a $K$-automorphism of $L$, and let $D$ be an idele Galois descent datum for $L/K$, i.e. a monoid homomorphism from $L\simeq_{\mathrm{alg}[K]}L$ to the ring automorphisms of the adele ring of $L$, compatible with the structure map from $L$ and acting continuously. Fix reals $c_L,u_L,d_{1L},d_{2L}$, a finite set $T_L\subseteq \mathrm{GL}_2(\mathbb{A}_L)$, and form the production pins of $L$ with domain $\bigcup_{x\in T_L}\{g x\}$ over the centre-cut Siegel set (finite part integral, all local heights $\ge c_L$, all window squares $\le u_L^2$, all archimedean determinant norms in $[d_{1L},d_{2L}]$), with level groups $N\mapsto \mathrm{levelOne}(N)\cap \ker(\mathrm{glArch})$, Hecke generators `heckeGen` at the finite places, and the adelic box as conditioning set; let $\xi_L$ be a character of the group $Z=\top$ of those pins. Let $N_K$ be an ideal of $\mathcal{O}_K$, $S_K$ a finite set of primes of $K$ containing every prime dividing $N_K$, $S_L$ a finite set of primes of $L$, $\Psi$ a Hecke eigensystem of $L$ over $\mathbb{C}$ (a nonzero level ideal together with families $a,b$), and $\mathrm{tys}_L$ a family of archimedean types of $L$ (finitely many representations at each infinite place). Write $V$ for the intersection of the $\mathbb{C}$-span of the isotypic cusp forms for these pins, $\xi_L$, the extended level $N_K\mathcal{O}_L$, $S_L$ and $\Psi$, with the archimedean cut submodule $\bigcap_w\sum_i \mathrm{archTypeSubmoduleAt}(w,\mathrm{tys}_L)$. Assume: $V$ is finite-dimensional over $\mathbb{C}$; for every $\varphi$ that is unit-factorizable above $K$ of type $\mathrm{tys}_L$ relative to the level group at $N_K\mathcal{O}_L$ and $S_K$, and every $u\in V$, the right convolution of $u\circ \mathrm{sigmaAdelicAct}(\sigma)$ against $\varphi$ again lies in $V$; and for every $u\in V$ the twist $u\circ\mathrm{sigmaAdelicAct}(\sigma)$ lies in the archimedean cut submodule. Then for every $u\in V$ the twist $u\circ \mathrm{sigmaAdelicAct}(\sigma)$ lies in $V$.
--
--   This is the passage from stability of the isotypic cusp space under the twisted convolution operators to stability under the Galois twist itself, obtained by approximating the twist by convolutions against test functions adapted to the level and the archimedean types and using that a finite-dimensional subspace is closed. It feeds into [`AutomorphicForm.exists_twistedCutTrace_ne_zero_of_pos_of_isArithGenuineCuspRealizable_of_isConstantOnFibers`](thm.html#AutomorphicForm.exists_twistedCutTrace_ne_zero_of_pos_of_isArithGenuineCuspRealizable_of_isConstantOnFibers), where a twisted trace on this space is shown to be non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sigmaSectionActOn_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.sigmaSectionActOn_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (Ψ : HeckeEigensystem L ℂ) (tysL : ArchTypeFamily L)
    (hfin : FiniteDimensional ℂ
      ↥(isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tysL))
    (hstab : ∀ φ : AdelicGL2 (𝓞 L) L → ℂ,
      IsUnitFactorizableAboveOfType K L tysL
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ →
      ∀ u ∈ isotypicCuspSubmodule L
            (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
              (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
              (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
          ⊓ archCutSubmodule L tysL,
        twistedConvOp K L D σ φ u ∈ isotypicCuspSubmodule L
            (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
              (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
              (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
          ⊓ archCutSubmodule L tysL)
    (harch : ∀ u ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tysL,
      sigmaSectionActOn K L D σ u ∈ archCutSubmodule L tysL) :
    ∀ u ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tysL,
      sigmaSectionActOn K L D σ u ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tysL := by sorry
