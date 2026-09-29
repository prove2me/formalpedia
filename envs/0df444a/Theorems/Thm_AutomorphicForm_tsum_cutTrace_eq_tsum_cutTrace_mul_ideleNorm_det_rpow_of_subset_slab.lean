-- Prove2me | Theorems.Thm_AutomorphicForm_tsum_cutTrace_eq_tsum_cutTrace_mul_ideleNorm_det_rpow_of_subset_slab
-- name    : AutomorphicForm.tsum_cutTrace_eq_tsum_cutTrace_mul_ideleNorm_det_rpow_of_subset_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/276f2286-0206-5d4c-9ac2-ffdc2322dba3
-- title:
--   Twist-invariance of summed cut cuspidal traces on GL₂
-- statement:
--   Let $K$ be a number field, and let $\Phi$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ which is assumed, via `hΦdet`, to lie in a determinant slab: there are reals $\alpha,\beta$ with $0<\alpha$ such that the idele norm $\|\det g\|$ — defined as the value of the distributive Haar character of $\mathbb{A}_K$ at $\det g$, viewed as a real number — lies in $[\alpha,\beta]$ for every $g\in\Phi$. Fix a finite set $S_K$ of finite places of $K$, an ideal $N$ of $\mathcal{O}_K$, an archimedean type family $\mathrm{tys}_K$ (a cardinality function on infinite places together with representations of the corresponding row-isometry subgroups), two homomorphisms $\xi_K,\xi_{0,K}$ from the full subgroup of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$, and $w\in\mathbb{R}$, such that $\xi_{0,K}(z)=\xi_K(z)\,\|z\|^{-w}$ for all ideles $z$. Let $f,f'$ be continuous compactly supported complex functions on $\mathrm{GL}_2(\mathbb{A}_K)$ with $f'(g)=f(g)\,\|\det g\|^{w/2}$ for all $g$. Throughout, the carrier data are the production pins built from $\Phi$ (as the distinguished set $D$), the level map $M\mapsto \mathrm{principalLevel}(M)\cap \ker(\mathrm{glArch})$, the Hecke generators $v\mapsto \mathrm{heckeGen}(v)$, and the box `adelicBox K` (whose conditioned additive Haar measure is the pins' measure $\nu$), with $Z=\top$, the Borel structures and the adelic Haar measures. The assertion is an equality of two unconditional sums: the sum over Hecke eigensystems $\pi$ (level ideal, a proof that it is nonzero, and eigenvalue functions $a,b$ on finite places) belonging to `cuspClasses` for $\xi_K$, i.e. with $\pi.\mathrm{level}=N$, $a_v=b_v=0$ for $v\in S_K$, and nonzero isotypic cusp submodule, of the cut trace $\mathrm{cutTrace}$ of $f$ — the trace of the convolution operator attached to $f$ on the intersection of the isotypic cusp submodule of $\pi$ with the archimedean cut submodule for $\mathrm{tys}_K$, taken to be $0$ unless that operator preserves the submodule — equals the corresponding sum, over the cusp classes for $\xi_{0,K}$, of the cut traces of $f'$.
--
--   This is the twisting relation $\xi\mapsto\xi\|\cdot\|^{-w}$, $f\mapsto f\,\|\det\|^{w/2}$ for the cut cuspidal traces of $\mathrm{GL}_2$ over a number field, allowing the central character to be normalised at the cost of a shift in the test function. It feeds the analytic continuation step in which the windowed Siegel/trace identities are compared along a vertical line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_tsum_cutTrace_eq_tsum_cutTrace_mul_ideleNorm_det_rpow_of_subset_slab.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.tsum_cutTrace_eq_tsum_cutTrace_mul_ideleNorm_det_rpow_of_subset_slab
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦdet : ∃ α β : ℝ, 0 < α ∧
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K)
    (ξK ξ₀K : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (w : ℝ)
    (hξ₀ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ξ₀K ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) =
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (-w) : ℝ) : ℂ))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (f' : AdelicGL2 (𝓞 K) K → ℂ) (hf' : Continuous f') (hfc' : HasCompactSupport f')
    (hff' : ∀ g : AdelicGL2 (𝓞 K) K,
      f' g = f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) :
    ∑' π : {π : HeckeEigensystem K ℂ //
        π ∈ cuspClasses K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK},
      cutTrace K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK π.1 tysK f hf hfc =
    ∑' π : {π : HeckeEigensystem K ℂ //
        π ∈ cuspClasses K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ₀K N SK},
      cutTrace K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ₀K N SK π.1 tysK f' hf' hfc' := by sorry
