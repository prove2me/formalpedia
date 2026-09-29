-- Prove2me | Theorems.Thm_AutomorphicForm_forall_exists_eLpNorm_axis_continuation_restrict_le_mul_pow_of_isCompact_of_ne_bot
-- name    : AutomorphicForm.forall_exists_eLpNorm_axis_continuation_restrict_le_mul_pow_of_isCompact_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/8f208db6-4439-5707-a85e-a21e9625e13f
-- title:
--   Polynomial local L² bounds for unitary GL₂ Eisenstein series
-- statement:
--   Let $K$ be a number field, $N \neq 0$ an ideal of $\mathcal{O}_K$, and $\mathrm{tysK}$ a family of archimedean types (a number $\mathrm{card}(w)$ of representations of the row-isometry group at each infinite place $w$). Write $\alpha_m$ for the module character of the adele ring $\mathbb{A}$, transported to a homomorphism $\mathbb{A}^\times \to \mathbb{R}^\times$, and assume it is everywhere positive. Given an index type $\iota_E$, families $\mu_e, \nu_e$ of characters of $\mathbb{A}^\times$ that are continuous, unitary ($|\mu_e(x)| = 1$ for all $x$) and trivial on the principal ideles $K^\times$, integers $n_e$, and functions $\varphi_{e,j} : \mathbb{C} \times GL_2(\mathbb{A}) \to \mathbb{C}$ ($j < n_e$) subject to: each $\varphi_{e,j}(s,\cdot)$ transforms under the adelic Borel (lower-left entry zero) by $b \mapsto \eta_1(b_{11})\eta_2(b_{22})$ with $\eta_1 = \mu_e \alpha_m^{s+1/2}$, $\eta_2 = \nu_e \alpha_m^{-(s+1/2)}$; archimedean $K$-finiteness (right translates under each $\mathrm{archRowIsometrySubgroup}$ span a finite-dimensional space, and uniformly in $s$ and $g$ inside one finite-dimensional $W$); $K_f$-smoothness (open stabiliser in the kernel of the archimedean projection); joint continuity in $(s,g)$ and holomorphy in $s$; flatness, i.e. $\varphi_{e,j}(s,k) = \varphi_{e,j}(0,k)$ for $k$ in the standard maximal compact subgroup; right invariance under $\mathrm{principalLevel}\,N$ intersected with the finite-adelic subgroup; membership in the type-cut submodule $\mathrm{archCutSubmodule}\,K\,\mathrm{tysK}$; and orthonormality of $\varphi_{e,i}(0,\cdot)$, $i < n_e$, for the Haar measure of the maximal compact subgroup. Suppose further that for each $e$ and each infinite place $w$ the local component of $\mu_e$ at $w$ is $x \mapsto \|x\|^{[K_w:\mathbb{R}]\,u_{\mu}(e,w)}(x/\|x\|)^{a_{\mu}(e,w)}$, and similarly for $\nu_e$ with $u_\nu, a_\nu$. Finally let $O_{e,j} \subseteq \mathbb{C}$ be open preconnected sets containing the imaginary axis and the half-plane $\operatorname{Re} s > 1/2$, and $E_{e,j}, N_{e,j}$ functions analytic in $s$ on $O_{e,j}$ for each $g$, continuous on $O_{e,j} \times GL_2(\mathbb{A})$, and satisfying for $\operatorname{Re} s > 1/2$ both $E_{e,j}(s,g) = \varphi_{e,j}(s,g) + \sum_{\xi \in K} \varphi_{e,j}(s, w_2 u(\xi) g)$ with $w_2$ the adelic Weyl element and $u(\xi)$ the unipotent matrix with upper-right entry $\xi$, and $N_{e,j}(s,g) = \int_{\mathbb{A}} \varphi_{e,j}(s, w_2^{-1}u(x)g)\,dx$ for the additive Haar measure. Then for every compact $C \subseteq GL_2(\mathbb{A})$ there are $c_0 \in \mathbb{R}$ and $A \in \mathbb{N}$ such that for all $e$, all $i < n_e$ and all $t \in \mathbb{R}$, the $L^2$ norm of $g \mapsto E_{e,i}(it, g)$ with respect to the Haar measure of $GL_2(\mathbb{A})$ restricted to $C$ is at most $c_0\bigl(1 + \sum_{w \mid \infty} |2it + u_\mu(e,w) - u_\nu(e,w)|\bigr)^A$.
--
--   This is the local square-integrability of unitary Eisenstein series on $GL_2$ over a number field, with a bound polynomial in the spectral parameter $it$ and with constants uniform over a family of sections of fixed level and fixed archimedean types whose characters vary. It supplies the $L^2$ input for the pairing identity between pseudo-Eisenstein series and truncated Eisenstein integrals used in the spectral decomposition step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_exists_eLpNorm_axis_continuation_restrict_le_mul_pow_of_isCompact_of_ne_bot.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
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
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.forall_exists_eLpNorm_axis_continuation_restrict_le_mul_pow_of_isCompact_of_ne_bot
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type)
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (uμ uν : ιE → InfinitePlace K → ℂ) (aμ aν : ιE → InfinitePlace K → ℤ)
      (_hμA : ∀ (e : ιE) (w : InfinitePlace K), LanglandsTunnell.Converse.IsArchCompAt K (μ e) w (uμ e w) (aμ e w))
      (_hνA : ∀ (e : ιE) (w : InfinitePlace K), LanglandsTunnell.Converse.IsArchCompAt K (ν e) w (uν e w) (aν e w))
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g)),
    ∀ (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C → ∃ (c₀ : ℝ) (A : ℕ),
      ∀ (e : ιE) (i : Fin (nE e)) (t : ℝ),
        eLpNorm (EE e i ((t : ℂ) * Complex.I)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) ≤
          ENNReal.ofReal
            (c₀ * (1 + ∑ w : InfinitePlace K, ‖2 * (t : ℂ) * Complex.I + (uμ e w - uν e w)‖) ^ A) := by sorry
