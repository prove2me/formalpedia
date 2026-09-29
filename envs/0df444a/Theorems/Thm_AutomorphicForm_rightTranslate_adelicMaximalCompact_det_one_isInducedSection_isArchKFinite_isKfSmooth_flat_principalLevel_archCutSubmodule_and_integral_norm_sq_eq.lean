-- Prove2me | Theorems.Thm_AutomorphicForm_rightTranslate_adelicMaximalCompact_det_one_isInducedSection_isArchKFinite_isKfSmooth_flat_principalLevel_archCutSubmodule_and_integral_norm_sq_eq
-- name    : AutomorphicForm.rightTranslate_adelicMaximalCompact_det_one_isInducedSection_isArchKFinite_isKfSmooth_flat_principalLevel_archCutSubmodule_and_integral_norm_sq_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/3f3e25dd-15c4-5bd1-86b6-6e2375a00102
-- title:
--   Right translation by K¹ preserves flat induced families and L²-norm
-- statement:
--   Let $K$ be a number field, $N$ an ideal of $\mathcal O_K$, and $\mathrm{tysK}$ a family assigning to each infinite place $w$ a finite list of archimedean representations of the row-isometry subgroup of $GL_2(K_w)$; the idele group carries its Borel measurable structure and the adele ring the Borel $\sigma$-algebra. Write $\alpha_m$ for the homomorphism $(\mathbb A_K)^\times \to \mathbb R^\times$ obtained from the distributive Haar character of the adele ring via $\mathbb R_{\ge 0}\to\mathbb R$, assumed everywhere positive, and let $\mu,\nu$ be characters $(\mathbb A_K)^\times\to\mathbb C^\times$. Let $\psi_s(g)$ be a family of functions on $GL_2(\mathbb A_K)$ such that for every $s$: $\psi_s(bg)=\eta_1(b_{00})\eta_2(b_{11})\psi_s(g)$ for $b$ in the subgroup of matrices with vanishing lower-left entry, where $\eta_1=\mu\cdot\alpha_m^{s+1/2}$ and $\eta_2=\nu\cdot\alpha_m^{-(s+1/2)}$; the right translates of $\psi_s$ under each archimedean row-isometry subgroup span a finite-dimensional space; the stabiliser of $\psi_s$ in the finite-adelic subgroup (the kernel of the archimedean projection) is open; $(s,g)\mapsto\psi_s(g)$ is continuous and $s\mapsto \psi_s(g)$ differentiable; at each infinite place $w$ there is a single finite-dimensional $W$ containing all functions $k\mapsto\psi_s(gk)$ on the row-isometry subgroup; $\psi_s=\psi_0$ on the maximal compact subgroup $\mathbf K$ (integral finite part, row-isometric archimedean parts); $\psi_s$ is invariant under right multiplication by the intersection of the principal level-$N$ subgroup with the finite-adelic subgroup; and $\psi_s$ lies in the cut submodule of $\mathrm{tysK}$, the intersection over infinite places of the sums of the listed type submodules. Then for $k\in\mathbf K$ whose archimedean component at every infinite place has determinant $1$, the family $x\mapsto\psi_s(xk)$ satisfies all nine of these conditions, and $\int_{\mathbf K}\|\psi_0(k'k)\|^2\,dk'=\int_{\mathbf K}\|\psi_0(k')\|^2\,dk'$ for the Haar measure on $\mathbf K$.
--
--   This is the stability of the class of flat, $K$-finite, $K_f$-smooth, level-$N$, fixed-type holomorphic families of sections of the induced representation $I(\mu\alpha^{s+1/2},\nu\alpha^{-(s+1/2)})$ under right translation by the determinant-one part of the adelic maximal compact subgroup, together with invariance of the $L^2(\mathbf K)$-norm at $s=0$. It feeds the uniform bounds on Whittaker coefficients of Bruhat–Eisenstein series, where an arbitrary element of $\mathbf K$ may be absorbed into the section without changing the hypotheses or the normalisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightTranslate_adelicMaximalCompact_det_one_isInducedSection_isArchKFinite_isKfSmooth_flat_principalLevel_archCutSubmodule_and_integral_norm_sq_eq.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.rightTranslate_adelicMaximalCompact_det_one_isInducedSection_isArchKFinite_isKfSmooth_flat_principalLevel_archCutSubmodule_and_integral_norm_sq_eq
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (k : AdelicGL2 (𝓞 K) K) (_hk : k ∈ adelicMaximalCompact K)
      (_hdet : ∀ w : InfinitePlace K,
        ((archComponent K w (glArch (𝓞 K) K k) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1),
    (∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (fun x => ψf s (x * k))) ∧
    (∀ s, IsArchKFinite K (fun x => ψf s (x * k))) ∧
    (∀ s, IsKfSmooth K (fun x => ψf s (x * k))) ∧
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 (p.2 * k)) ∧
    (∀ g, Differentiable ℂ (fun s => ψf s (g * k))) ∧
    (∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        (fun k' : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k' : AdelicGL2 (𝓞 K) K) * k)) ∈ W) ∧
    (∀ (s : ℂ) (k' : adelicMaximalCompact K),
      ψf s ((k' : AdelicGL2 (𝓞 K) K) * k) = ψf 0 ((k' : AdelicGL2 (𝓞 K) K) * k)) ∧
    (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
      ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u * k) = ψf s (g * k)) ∧
    (∀ s : ℂ, (fun x => ψf s (x * k)) ∈ archCutSubmodule K tysK) ∧
    (∫ k', ‖ψf 0 ((k' : AdelicGL2 (𝓞 K) K) * k)‖ ^ 2 ∂(maximalCompactHaar K)
      = ∫ k', ‖ψf 0 (k' : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) := by sorry
