-- Prove2me | Theorems.Thm_AutomorphicForm_forall_exists_setIntegral_norm_sq_lambdaT_axis_continuation_le_mul_mul_pow_of_isArchCompAt_of_ne_bot
-- name    : AutomorphicForm.forall_exists_setIntegral_norm_sq_lambdaT_axis_continuation_le_mul_mul_pow_of_isArchCompAt_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/fc3f0601-8fc5-5081-b28b-857815b6433a
-- title:
--   Uniform L² bound for truncated Eisenstein series on the unitary axis
-- statement:
--   Let $K$ be a number field, $N$ a nonzero ideal of $\mathcal O_K$ and $\mathrm{tysK}$ a family of archimedean types (for each infinite place $w$, a finite list of representations of the row‑isometry group at $w$). Write $\alpha_m$ for the idele‑class character obtained from the module character `distribHaarChar` of the adele ring, valued in $\mathbb R^\times$, and assume it is everywhere positive. Given an index type $\iota_E$, families $\mu,\nu:\iota_E\to$ characters of the idele group that are unitary ($\|\mu_e(x)\|=1$), trivial on principal ideles and continuous; integers $n_e$; and functions $\varphi_{e,j}:\mathbb C\times GL_2(\mathbb A_K)\to\mathbb C$ satisfying: $\varphi_{e,j}(s,\cdot)$ is a section induced from $(\mu_e\alpha_m^{s+1/2},\nu_e\alpha_m^{-(s+1/2)})$, i.e. $\varphi(bg)=\mu_e\alpha_m^{s+1/2}(b_{11})\,\nu_e\alpha_m^{-(s+1/2)}(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; archimedean $K$‑finiteness at every infinite place and smoothness under the finite‑adelic subgroup (the kernel of `glArch`); joint continuity in $(s,g)$ and holomorphy in $s$; a uniform version of archimedean $K$‑finiteness, a single finite‑dimensional space of functions on the row‑isometry subgroup at $w$ containing all right translates $k\mapsto\varphi_{e,j}(s,gk)$; flatness, $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ on the maximal compact subgroup `adelicMaximalCompact`; right invariance under `principalLevel` $N$ intersected with the finite‑adelic subgroup; membership in the type‑cut submodule `archCutSubmodule K tysK`; and orthonormality $\int_{\mathbf K}\varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}\,dk=\delta_{ij}$ for the Haar probability measure of that compact group. Let $u_{\mu},u_{\nu}:\iota_E\to\mathrm{InfinitePlace}(K)\to\mathbb C$ and $a_\mu,a_\nu$ integer valued satisfy `IsArchCompAt`, i.e. the local component of $\mu_e$ at $w$ is $x\mapsto\|x\|^{\mathrm{mult}(w)u_\mu(e,w)}(x/\|x\|)^{a_\mu(e,w)}$, and likewise for $\nu_e$. Finally let $O_{e,j}\subseteq\mathbb C$ be open and preconnected, containing the imaginary axis and the half‑plane $\operatorname{Re}s>1/2$, and let $E_{e,j},N_{e,j}$ be analytic on a neighbourhood of $O_{e,j}$ in $s$ for each $g$, continuous on $O_{e,j}\times GL_2(\mathbb A_K)$, and agree for $\operatorname{Re}s>1/2$ with the Eisenstein series $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}\varphi_{e,j}(s,w\,n(\xi)g)$ and with the Weyl intertwining integral $N_{e,j}(s,g)=\int\varphi_{e,j}(s,w^{-1}n(x)g)\,dx$ against the additive adelic Haar measure. Then for all reals $0<\alpha<\beta$ and every set $\Phi_F$ of adelic matrices there exist $c,R_0\in\mathbb R$ and $A\in\mathbb N$ such that for all $e$, all $i<n_e$, all $t\in\mathbb R$ and all $R\ge R_0$ the function $x\mapsto\|(\Lambda^{e^R}E_{e,i}(it))(x)\|^2$ is integrable over `canonicalTruncationDomain K α β` for the Haar measure of $GL_2(\mathbb A_K)$, with $$\int_{\mathrm{canonicalTruncationDomain}}\bigl\|\Lambda^{e^R}E_{e,i}(it)\bigr\|^2 \le c\,(|R|+1)\Bigl(1+\sum_{w\mid\infty}\bigl\|2it+u_\mu(e,w)-u_\nu(e,w)\bigr\|\Bigr)^A .$$ Here $\Lambda^{T}$ is `lambdaT`: subtraction, on the locus where the adelic height `adelicHeight K` exceeds $T=e^R$, of the constant term along $x\mapsto$ `unipotentGL2` $x$ taken against the measure field of `productionPinsOf`, namely the additive adelic Haar measure conditioned on `adelicBox`; of the data packaged in those pins only the Borel structure on the adele ring and this measure enter, so $\Phi_F$ and the chosen level and Hecke generators are inert.
--
--   This is the family‑uniform form of the classical Maass–Selberg estimate for the truncated Eisenstein series of $GL_2$ on the unitary axis: growth linear in the truncation parameter $R$ and polynomial in the spectral gauge $1+\sum_w\|2it+u_\mu-u_\nu\|$, with constants depending only on the level, the archimedean types and the truncation slab, not on the member of the family nor on the central characters. It feeds the construction of the continuous part of the spectral decomposition, being cited in the production of $L^2$ truncated wave packets matched to a Paley–Wiener datum and in the uniform $L^p$‑norm bound for the analytic continuation restricted to compact sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_exists_setIntegral_norm_sq_lambdaT_axis_continuation_le_mul_mul_pow_of_isArchCompAt_of_ne_bot.lean

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

theorem AutomorphicForm.forall_exists_setIntegral_norm_sq_lambdaT_axis_continuation_le_mul_mul_pow_of_isArchCompAt_of_ne_bot
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
    ∀ (α β : ℝ), 0 < α → α < β → ∀ (ΦF : Set (AdelicGL2 (𝓞 K) K)),
    ∃ (c R₀ : ℝ) (A : ℕ), ∀ (e : ιE) (i : Fin (nE e)) (t R : ℝ), R₀ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K =>
          ‖@AutomorphicForm.lambdaT _
          (productionPinsOf K ΦF (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦF (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (EE e i ((t : ℂ) * Complex.I)) x‖ ^ 2)
        (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
      ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
          ‖@AutomorphicForm.lambdaT _
          (productionPinsOf K ΦF (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦF (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (EE e i ((t : ℂ) * Complex.I)) x‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤
        c * (|R| + 1) * (1 + ∑ w : InfinitePlace K, ‖2 * (t : ℂ) * Complex.I + (uμ e w - uν e w)‖) ^ A := by sorry
