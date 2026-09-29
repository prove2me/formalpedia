-- Prove2me | Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_twist_mul_ideleNorm_det_rpow_of_subset_slab
-- name    : AutomorphicForm.isIsotypicCuspFormAt_twist_mul_ideleNorm_det_rpow_of_subset_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/01043439-fd46-5e30-b4c8-1316c5758a18
-- title:
--   Twisting an isotypic cusp form by ‖det‖^{-w/2}
-- statement:
--   Let $K$ be a number field and let $\Phi$ be a set of elements of $\mathrm{GL}_2$ of the adele ring of $K$ which is contained in a determinant slab: there are reals $\alpha,\beta$ with $0<\alpha$ such that every $g\in\Phi$ satisfies $\alpha\le\|\det g\|\le\beta$, where $\|\cdot\|$ denotes [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the module of an idele measured by the distributive Haar character. Let $S_K$ be a finite set of finite places of $K$, $N$ an ideal of $\mathcal O_K$, and let $\xi_K,\xi_{0,K}$ be characters $\top\to\mathbb C^\times$ of the full unit group of the adele ring, related by $\xi_{0,K}(z)=\xi_K(z)\,\|z\|^{-w}$ for all ideles $z$, for a fixed $w\in\mathbb R$. Let $\pi$ be a Hecke eigensystem over $\mathbb C$, that is, a nonzero level ideal together with families $a_v,b_v\in\mathbb C$ indexed by the finite places, and let $\varphi$ be a complex-valued function on $\mathrm{GL}_2$ of the adeles. The carrier data used throughout is `productionPinsOf` applied to $\Phi$, to the level subgroups $M\mapsto$ `principalLevel` at $M$ intersected with the kernel of the archimedean projection, to the Hecke generators `heckeGen` at each finite place, and to the box `adelicBox` $K$: so the Borel structure and Haar measure on $\mathrm{GL}_2$ of the adeles, the carrier $\Phi$, the central subgroup $\top$, those level subgroups and generators, and the adelic additive Haar measure conditioned on `adelicBox` $K$. Assume `IsIsotypicCuspFormAt` holds for $(\xi_K,N,S_K,\pi,\varphi)$ with respect to these data, i.e. $\varphi$ satisfies the predicate `IsSmoothCuspAutomorphicFnAt` for $\xi_K$, is continuous, is right invariant under the level subgroup at $N$, is a Hecke coset eigenfunction at each $v\notin S_K$ with eigenvalue $\pi.a\,v$ (in the sense of `SmoothCusp.IsHeckeCosetEigenfunctionAt` for the generator `heckeGen` at $v$), and satisfies $\varphi(\mathrm{diag}(\det(\mathrm{heckeGen}\,v))\cdot g)=(\mathrm{cNorm}\,v)^{-1}\,\pi.b\,v\cdot\varphi(g)$ for all $g$ and all $v\notin S_K$. The conclusion is that the same predicate holds, with respect to the same carrier data, for the character $\xi_{0,K}$, the same $N$ and $S_K$, the twisted eigensystem `π.twist χ` with $\chi(v)=\|\det(\mathrm{heckeGen}\,v)\|^{-w/2}$ (same level, $a_v\mapsto\chi(v)a_v$, $b_v\mapsto\chi(v)^2b_v$), and the function $g\mapsto\varphi(g)\,\|\det g\|^{-w/2}$.
--
--   This is the standard normalisation move on automorphic forms for $\mathrm{GL}_2$ over a number field: multiplying by a real power of the idele norm of the determinant shifts the central character by $\|\cdot\|^{-w}$ and twists the Hecke eigenvalues by $\chi$ and $\chi^2$ respectively, the restriction of the carrier to a determinant slab guaranteeing that the twisting factor stays bounded there. It is used in the comparison of cusp classes and their cut traces under such a twist, the statement [`AutomorphicForm.mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab`](thm.html#AutomorphicForm.mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isIsotypicCuspFormAt_twist_mul_ideleNorm_det_rpow_of_subset_slab.lean

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

theorem AutomorphicForm.isIsotypicCuspFormAt_twist_mul_ideleNorm_det_rpow_of_subset_slab
    (K : Type) [Field K] [NumberField K]
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦdet : ∃ α β : ℝ, 0 < α ∧
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K))
    (ξK ξ₀K : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (w : ℝ)
    (hξ₀ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ξ₀K ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) =
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (-w) : ℝ) : ℂ))
    (π : HeckeEigensystem K ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsIsotypicCuspFormAt K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK π φ) :
    IsIsotypicCuspFormAt K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ₀K N SK
      (π.twist (fun v : HeightOneSpectrum (𝓞 K) =>
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))) ^ (-(w / 2)) : ℝ) : ℂ)))
      (fun g : AdelicGL2 (𝓞 K) K => φ g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ)) := by sorry
