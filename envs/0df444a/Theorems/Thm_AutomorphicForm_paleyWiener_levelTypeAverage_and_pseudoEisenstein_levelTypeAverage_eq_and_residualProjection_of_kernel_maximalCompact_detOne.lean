-- Prove2me | Theorems.Thm_AutomorphicForm_paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne
-- name    : AutomorphicForm.paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/9908e5f9-4a1c-5108-ac24-fe53a5a50c4a
-- title:
--   Transport of Paley–Wiener data by a maximal-compact kernel average
-- statement:
--   Fix a number field $K$, real numbers $\alpha<\beta$ with $0<\alpha$, a homomorphism $\xi_K$ from the full subgroup of idèles $(\mathbb{A}_K^\times)$ to $\mathbb{C}^\times$, an ideal $N$ of $\mathcal{O}_K$ and an archimedean type family $\mathrm{tysK}$ (for each infinite place $w$ a finite list of representations of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$). The central character is assumed continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on the image of $K^\times$ (`hξt`) and unitary, $\lVert\xi_K(z)\rVert=1$ for all idèles $z$ (`hξu`).
--
--   The statement introduces $\alpha_m$, the character of the idèles obtained from the modulus character `distribHaarChar` of $\mathbb{A}_K$ with values in $\mathbb{R}_{\ge 0}$, pushed into $\mathbb{R}^\times$, the adeles carrying their Borel $\sigma$-algebra; `hαm` requires $\alpha_m(x)>0$ for every $x$.
--
--   The averaging operator is given by a continuous function $\kappa$ on the adelic maximal compact $\mathbf{K}=\mathrm{adelicMaximalCompact}\,K$ (the matrices whose finite part is integral and whose archimedean component at each infinite place $w$ is a row isometry) together with an operator $P$ on $\mathbb{C}$-valued functions on $\mathrm{GL}_2(\mathbb{A}_K)$ such that $P\varphi(g)=\int_{\mathbf{K}}\kappa(k)\,\varphi(gk)\,dk$ for the Haar measure `maximalCompactHaar` (`_hP`). Four further groups of hypotheses on $P$ are imposed. Range (`_hPrange`): for continuous, archimedean $K$-finite $\varphi$ (finitely many right translates under the row-isometry subgroup at each infinite place span a finite-dimensional space), $P\varphi$ is continuous, archimedean $K$-finite, invariant under right translation by every $u$ in $\mathrm{principalLevel}\,N$ intersected with the kernel of the archimedean projection $\mathrm{glArch}$, and lies in the archimedean type cut $\mathrm{archCutSubmodule}\,K\,\mathrm{tysK}$ (the intersection over infinite places of the sums of the type submodules attached to the given representations). Commutation (`_hPcomm`): for $k\in\mathbf{K}$ whose archimedean component has determinant $1$ at every real place, $P(\varphi(\cdot\,k))(g)=P\varphi(gk)$. Automorphy and self-adjointness (`_hPaut`): if $\varphi$ and $\psi$ both satisfy the automorphy predicate `IsAutomorphicFnAt` for the carrier data $\mathrm{productionPinsOf}$ attached to the canonical truncation domain $\Phi_0=\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta$, the levels $M\mapsto\mathrm{principalLevel}\,M\sqcap\ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}$, the box $\mathrm{adelicBox}\,K$, the adelic Haar measure on $\mathrm{GL}_2$, the full central subgroup $Z=\top$ and the conditional additive Haar measure on the box, and the character $\xi_K$, then $P\varphi$ satisfies the same predicate and $\int_{\Phi_0}P\varphi\,\overline{\psi}=\int_{\Phi_0}\varphi\,\overline{P\psi}$ for the adelic Haar measure. Residual stability (`_hPres`): if $h$ is automorphic in the above sense and lies in $\mathrm{residualSpan}$, the $\mathbb{C}$-span of the functions $g\mapsto\chi(\det g)$ for characters $\chi$ of the idèles with $\chi^2=\xi_K$ on $Z$, then $P h$ lies in that span.
--
--   The Paley–Wiener datum consists of a finite index type $\iota_P$, families $\mu^P,\nu^P:\iota_P\to\mathrm{Hom}((\mathbb{A}_K^\times),\mathbb{C}^\times)$, a map $r_P:\iota_P\to\iota_P$, a family of sections $\psi_f$ and a function $\psi$. The character hypotheses are: each $\mu^P_e$ and $\nu^P_e$ is unitary (`_hμ`, `_hν`) and trivial on the image of $K^\times$ (`_hμic`, `_hνic`); $\mu^P_e$ and $\nu^P_e$ are continuous (`_hμc`, `_hνc`); $\mu^P_e(z)\nu^P_e(z)=\xi_K(z)$ for all $z\in Z$ (`_hμν`); $\mu^P_{r_Pe}=\nu^P_e$ and $\nu^P_{r_Pe}=\mu^P_e$ (`_hr`); and distinct indices are separated by some idèle of norm one, i.e. in the kernel of `distribHaarChar` (`_hdist`). The section hypotheses are: for all $e$ and $s\in\mathbb{C}$, $\psi_f(e,s)$ is an induced section for the pair $\bigl(\mu^P_e\cdot\alpha_m^{\,s+1/2},\ \nu^P_e\cdot\alpha_m^{-(s+1/2)}\bigr)$, that is $\psi_f(e,s)(bg)=\eta_1(b_{11})\eta_2(b_{22})\psi_f(e,s)(g)$ for $b$ in the adelic Borel subgroup (lower-left entry zero) (`_hψf`); joint continuity in $(s,g)$ (`_hψjc`); holomorphy of $s\mapsto\psi_f(e,s)(g)$ (`_hψhol`); archimedean $K$-finiteness (`_hψK`) and smoothness as a vector for the finite-adelic subgroup (`_hψsm`); a uniform $K$-type bound (`_hψKu`): for each $e$ and each infinite place $w$ there is a finite-dimensional subspace $W$ of functions on the archimedean row-isometry subgroup at $w$ containing all functions $k\mapsto\psi_f(e,s)(gk)$, for all $s$ and $g$; and vertical decay (`_hψdec`): for each $e$, each $n\in\mathbb{N}$, each $\sigma_0$ and each compact $C$ there is an integrable, bounded above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\lVert\psi_f(e,\sigma'+it)(g)\rVert\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. Finally $\psi$ is a slab profile for $Z$ and $\xi_K$ (`_hψ`): measurable, invariant under left translation by unipotent adelic matrices and by global Borel points, transforming by $\xi_K$ under the central scalars, bounded on each slab $\{\,\lVert\det g\rVert\in[d_1,d_2]\}$ with $d_1>0$, and supported where the adelic height lies in a band $[a,b]$ with $a>0$; and $\psi$ admits the contour representation $\psi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb{R}}\psi_f(e,\sigma'+it)(g)\,dt$ for every $\sigma'\in\mathbb{R}$ and every $g$ (`_hψrep`).
--
--   The conclusion is the conjunction of thirteen assertions. (1) For all $e$ and $s$, $P(\psi_f(e,s))$ is an induced section for the same pair of characters $\bigl(\mu^P_e\cdot\alpha_m^{\,s+1/2},\ \nu^P_e\cdot\alpha_m^{-(s+1/2)}\bigr)$. (2) For each $e$, $(s,g)\mapsto P(\psi_f(e,s))(g)$ is continuous. (3) For each $e$ and $g$, $s\mapsto P(\psi_f(e,s))(g)$ is holomorphic on $\mathbb{C}$. (4) Each $P(\psi_f(e,s))$ is archimedean $K$-finite. (5) Each $P(\psi_f(e,s))$ is smooth for the finite-adelic subgroup. (6) For each $e$ and each infinite place $w$ there is a finite-dimensional space of functions on the archimedean row-isometry subgroup at $w$ containing all $k\mapsto P(\psi_f(e,s))(gk)$, uniformly in $s$ and $g$. (7) The same vertical decay estimate as `_hψdec`, with $P(\psi_f(e,\sigma'+it))$ in place of $\psi_f(e,\sigma'+it)$. (8) $P\psi$ is a slab profile for $Z$ and $\xi_K$. (9) For every $\sigma'$ and $g$, $P\psi(g)=\sum_e(4\pi)^{-1}\int_{\mathbb{R}}P(\psi_f(e,\sigma'+it))(g)\,dt$. (10) Each $P(\psi_f(i,s))$ is invariant under right translation by elements of $\mathrm{principalLevel}\,N$ intersected with the kernel of $\mathrm{glArch}$. (11) Each $P(\psi_f(i,s))$ lies in $\mathrm{archCutSubmodule}\,K\,\mathrm{tysK}$. (12) The pseudo-Eisenstein series commute with $P$ as functions: $\mathrm{pseudoEisenstein}\,K\,(P\psi)=P(\mathrm{pseudoEisenstein}\,K\,\psi)$, where $\mathrm{pseudoEisenstein}\,K\,\varphi(g)=\varphi(g)+\sum_{\beta\in K}'\varphi(w\,u(\beta)\,g)$ with $w$ the adelic Weyl element and $u(\beta)$ the unipotent matrix with upper-right entry $\beta$. (13) Residual projections are transported: for every $p$, if $p$ is automorphic for the above carrier data and $\xi_K$, if for every $\varepsilon>0$ there is an automorphic $r$ in the residual span with $\lVert p-r\rVert_{L^2}<\varepsilon$ for the Haar measure restricted to $\Phi_0$, and if $\int_{\Phi_0}(\mathrm{pseudoEisenstein}\,K\,\psi-p)\overline{h}=0$ for every automorphic $h$ in the residual span, then the same three properties hold for $P p$: it is automorphic, it is an $L^2(\Phi_0)$-limit of automorphic elements of the residual span, and $\int_{\Phi_0}(\mathrm{pseudoEisenstein}\,K\,(P\psi)-P p)\overline{h}=0$ for every automorphic $h$ in the residual span.
--
--   This is the transport statement for strong Paley–Wiener data under a right convolution by a continuous kernel on the adelic maximal compact subgroup: the characters $\mu^P,\nu^P$ and the involution $r_P$ are unchanged, the averaged sections acquire right invariance at level $N$ and the prescribed archimedean types, pseudo-Eisenstein series commute with the averaging, and residual projections are carried to residual projections. It is used in the density and orthogonality steps for pseudo-Eisenstein series, namely by [`AutomorphicForm.exists_matched_paleyWiener_forall_norm_setIntegral_sub_pseudoEisenstein_sub_mul_conj_le_of_orthogonal`](thm.html#AutomorphicForm.exists_matched_paleyWiener_forall_norm_setIntegral_sub_pseudoEisenstein_sub_mul_conj_le_of_orthogonal) and [`AutomorphicForm.forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero`](thm.html#AutomorphicForm.forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne.lean

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
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (κ : ↥(adelicMaximalCompact K) → ℂ) (_hκ : Continuous κ)
      (P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
      (_hP : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
        P φ g = ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      (_hPrange : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ →
        Continuous (P φ) ∧ IsArchKFinite K (P φ) ∧ (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, (P φ) (g * u) = (P φ) g) ∧ P φ ∈ archCutSubmodule K tysK)
      (_hPcomm : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (k : ↥(adelicMaximalCompact K)),
        (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
        ∀ g : AdelicGL2 (𝓞 K) K, P (fun x => φ (x * (k : AdelicGL2 (𝓞 K) K))) g = P φ (g * (k : AdelicGL2 (𝓞 K) K)))
      (_hPaut : ∀ φ ψ : AdelicGL2 (𝓞 K) K → ℂ,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ → IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ψ →
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (P φ) ∧
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, P φ g * conj (ψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, φ g * conj (P ψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
      (_hPres : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        P h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK)
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g),
    (∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (P (ψf e s))) ∧
    (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => P (ψf e p.1) p.2)) ∧
    (∀ e g, Differentiable ℂ (fun s => P (ψf e s) g)) ∧
    (∀ e s, IsArchKFinite K (P (ψf e s))) ∧
    (∀ e s, IsKfSmooth K (P (ψf e s))) ∧
    (∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => P (ψf e s) (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
    (∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖P (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g‖ ≤ m t) ∧
    (AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK (P ψ)) ∧
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        P ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, P (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g) ∧
    (∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, P (ψf i s) (g * u) = P (ψf i s) g) ∧
    (∀ i (s : ℂ), P (ψf i s) ∈ archCutSubmodule K tysK) ∧
    AutomorphicForm.pseudoEisenstein K (P ψ) = P (AutomorphicForm.pseudoEisenstein K ψ) ∧
    (∀ p : AdelicGL2 (𝓞 K) K → ℂ,
      (IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p ∧
        (∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
          IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (p - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε) ∧
        (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (AutomorphicForm.pseudoEisenstein K ψ g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)) →
      (IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (P p) ∧
        (∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
          IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm ((P p) - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε) ∧
        (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (AutomorphicForm.pseudoEisenstein K (P ψ) g - (P p) g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0))) := by sorry
