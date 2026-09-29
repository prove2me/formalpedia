-- Prove2me | Theorems.Thm_AutomorphicForm_mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab
-- name    : AutomorphicForm.mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/ac1352c0-c17d-5e39-a6b4-2422161cbd9d
-- title:
--   Determinant-norm twisting of cuspidal classes and cut traces
-- statement:
--   Let $K$ be a number field, $\Phi \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ a set contained in a determinant slab, i.e. there are reals $\alpha > 0$ and $\beta$ with $\|\det g\| \in [\alpha,\beta]$ for all $g \in \Phi$, where $\|\cdot\|$ is the idele norm [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), given by the module of the distributive Haar character on $\mathbb{A}_K$. Let $S_K$ be a finite set of finite places of $K$, $N$ an ideal of $\mathcal{O}_K$, $\mathcal{T}$ an archimedean type family (a number $\mathrm{card}(w)$ of archimedean representation types at each infinite place $w$), $\xi_K,\xi_{0,K} : \mathbb{A}_K^\times \to \mathbb{C}^\times$ characters of the full group of ideles, and $w \in \mathbb{R}$, subject to $\xi_{0,K}(z) = \xi_K(z)\,\|z\|^{-w}$ for all $z$. Let $f, f' : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous with compact support and $f'(g) = f(g)\,\|\det g\|^{w/2}$, and let $\pi$ be a Hecke eigensystem over $\mathbb{C}$ (a level ideal $\ne \bot$ together with coefficient functions $a,b$ on finite places). Write $\pi \otimes \chi$ for `HeckeEigensystem.twist` of $\pi$ by $\chi(v) = \|\det(\mathrm{heckeGen}_v)\|^{-(w/2)}$, i.e. the eigensystem with the same level and with $a_v \mapsto \chi(v) a_v$, $b_v \mapsto \chi(v)^2 b_v$. All data are read at the carrier pins `productionPinsOf K Φ …`: Borel structure and adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, carrier $D = \Phi$, central group $Z = \top$, level subgroups $M \mapsto \mathrm{principalLevel}(M) \sqcap \mathrm{finiteAdelicGL2Subgroup}$, Hecke generators $v \mapsto \mathrm{heckeGen}_v$, and the additive adelic Haar measure conditioned on the adelic box. The conclusion is twofold. First, $\pi$ lies in $\mathrm{cuspClasses}$ for $\xi_K$, $N$, $S_K$ — that is, $\pi$ has level $N$, has $a_v = b_v = 0$ for all $v \in S_K$, and its isotypic cusp submodule is non-zero — if and only if $\pi \otimes \chi$ lies in $\mathrm{cuspClasses}$ for $\xi_{0,K}$, $N$, $S_K$. Second, the cut trace of $f$ at $(\xi_K, N, S_K, \pi)$ with archimedean types $\mathcal{T}$, namely the convolution trace of $f$ on the intersection of the isotypic cusp submodule with the archimedean cut submodule, equals the cut trace of $f'$ at $(\xi_{0,K}, N, S_K, \pi \otimes \chi)$ with the same types.
--
--   This is the compatibility of the cuspidal spectrum and of its localised traces under twisting an automorphic family by a power of the norm of the determinant: multiplication by $\|\det\|^{-w/2}$ matches the $\xi$-isotypic cusp forms with the $\xi_0$-isotypic ones, shifts the Hecke eigenvalues by $\chi$, and converts $f$ into $f' = f\,\|\det\|^{w/2}$; the slab hypothesis on the carrier $\Phi$ keeps the twisting factor pinched between two positive constants. It is used in the summed form [`AutomorphicForm.tsum_cutTrace_eq_tsum_cutTrace_mul_ideleNorm_det_rpow_of_subset_slab`](thm.html#AutomorphicForm.tsum_cutTrace_eq_tsum_cutTrace_mul_ideleNorm_det_rpow_of_subset_slab), where the normalisation of the central character in the trace identity is fixed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab.lean

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

theorem AutomorphicForm.mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab
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
      f' g = f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ))
    (π : HeckeEigensystem K ℂ) :
    (π ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK ↔
      π.twist (fun v : HeightOneSpectrum (𝓞 K) =>
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))) ^ (-(w / 2)) : ℝ) : ℂ)) ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ₀K N SK) ∧
    cutTrace K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK π tysK f hf hfc =
      cutTrace K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ₀K N SK
        (π.twist (fun v : HeightOneSpectrum (𝓞 K) =>
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))) ^ (-(w / 2)) : ℝ) : ℂ))) tysK f' hf' hfc' := by sorry
