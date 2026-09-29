-- Prove2me | Theorems.Thm_AutomorphicForm_exists_paleyWiener_oneIndex_apply_diagOne_mul_eq_of_isInducedSection_of_contDiff_of_pos
-- name    : AutomorphicForm.exists_paleyWiener_oneIndex_apply_diagOne_mul_eq_of_isInducedSection_of_contDiff_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/2a35cb35-c1cd-5cf9-958e-bef866b7440f
-- title:
--   One-index Paley–Wiener slab profile with prescribed torus values
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ obtained from the module character `distribHaarChar` of the adele ring, viewed as a homomorphism into $\mathbb{R}^\times$, with $\alpha(x)>0$ for all $x$ (hypothesis $h\alpha$). Fix a set $\Phi \subseteq \mathrm{GL}_2(\mathbb{A}_F)$; the pin data `productionPinsOf` built from $\Phi$, the level-one subgroups, the Hecke generators and the adelic box has central subgroup $Z = \top$, so a character $\xi$ of it is a character of the whole idele group. Let $\mu,\nu$ be characters of $(\mathbb{A}_F)^\times$ into $\mathbb{C}^\times$ that are unitary ($|\mu(x)|=|\nu(x)|=1$), trivial on the principal ideles $F^\times$, continuous, and satisfy $\mu(z)\nu(z)=\xi(z)$ for all $z \in Z$. Let $\varphi_0 : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous and an induced section for the pair $(\mu\,\alpha^{\,1/2}, \nu\,\alpha^{-1/2})$, i.e. $\varphi_0(bg) = \chi_1(b_{11})\chi_2(b_{22})\varphi_0(g)$ for $b$ in the adelic Borel subgroup (lower-left entry zero), with $\chi_1 = \mathrm{etaFst}\,\mu\,\alpha\,h\alpha\,0$ and $\chi_2 = \mathrm{etaSnd}\,\nu\,\alpha\,h\alpha\,0$; assume further that at each infinite place $w$ the right translates of $\varphi_0$ by `archRowIsometrySubgroup F w` span a finite-dimensional space, and that the stabiliser of $\varphi_0$ in the finite-adelic subgroup (the kernel of `glArch`) is open. Let $a,b>0$, and let $h_1 : \mathbb{R} \to \mathbb{C}$ be $C^\infty$ with compact support and $h_1(u)=0$ outside $[\log a, \log b]$. Then there exist $\hat\psi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ and $\psi_0 : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ such that: each $\hat\psi(s)$ is an induced section for $(\mathrm{etaFst}\,\mu\,\alpha\,h\alpha\,s, \mathrm{etaSnd}\,\nu\,\alpha\,h\alpha\,s)$; $(s,g) \mapsto \hat\psi(s)(g)$ is continuous; $s \mapsto \hat\psi(s)(g)$ is entire for each $g$; each $\hat\psi(s)$ is archimedean row-isometry finite and $K_f$-smooth; for each infinite place $w$ there is one finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup F w` containing $k \mapsto \hat\psi(s)(gk)$ for all $s$ and $g$; for every $m_0 \in \mathbb{N}$, $\sigma_0 \in \mathbb{R}$ and compact $C$ there is an integrable, bounded $m : \mathbb{R} \to \mathbb{R}$ with $(1+|t|)^{m_0}\,\|\hat\psi(\sigma'+it)(g)\| \le m(t)$ whenever $|\sigma'| \le \sigma_0$, $t \in \mathbb{R}$, $g \in C$; $\psi_0$ is a slab profile for $\xi$ (measurable, invariant under left translation by adelic unipotents and by rational Borel points, transforming by $\xi$ under the central scalars of $Z$, bounded on each set where the idele norm of the determinant lies in $[d_1,d_2]$ with $d_1>0$, and supported where the adelic height lies in some band); $\psi_0(g) = (4\pi)^{-1}\int_{\mathbb{R}} \hat\psi(\sigma'+it)(g)\,dt$ for every $\sigma' \in \mathbb{R}$; $\psi_0(g) \neq 0$ implies $\mathrm{adelicHeight}_F(g) \in [a,b]$; and finally, for every idele $y$ and every $k$ whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place is a row isometry, $$\psi_0(\mathrm{diag}(y,1)\,k) = \mu(y)\,h_1(\log \|y\|)\,\varphi_0(k),$$ where $\|y\|$ is the idele norm [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19).
--
--   This constructs a single index of a Paley–Wiener datum: an entire flat family of induced sections on vertical lines, together with the slab profile obtained by contour integration, whose values on the product of the one-parameter diagonal torus with the adelic maximal compact are the prescribed elementary function $\mu(y)h_1(\log\|y\|)\varphi_0(k)$. It is used in the proof that Paley–Wiener slab profiles are dense among slab profiles, and its output feeds the assembly of finite sums of such data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_paleyWiener_oneIndex_apply_diagOne_mul_eq_of_isInducedSection_of_contDiff_of_pos.lean

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem AutomorphicForm.exists_paleyWiener_oneIndex_apply_diagOne_mul_eq_of_isInducedSection_of_contDiff_of_pos
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hμν : ∀ z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z, μ (z : (AdeleRing (𝓞 F) F)ˣ) * ν (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z)
      (φ₀ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα 0) (etaSnd ν α hα 0) φ₀)
      (_hφ₀K : IsArchKFinite F φ₀) (_hφ₀f : IsKfSmooth F φ₀) (_hφ₀c : Continuous φ₀)
      (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b)
      (h₁ : ℝ → ℂ) (_hh₁ : ContDiff ℝ (⊤ : ℕ∞) h₁) (_hh₁c : HasCompactSupport h₁)
      (_hh₁b : ∀ u : ℝ, h₁ u ≠ 0 → u ∈ Set.Icc (Real.log a) (Real.log b)),
    ∃ (ψf₀ : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (ψ₀ : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψf₀ s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf₀ p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => ψf₀ s g)) ∧
      (∀ s, IsArchKFinite F (ψf₀ s)) ∧ (∀ s, IsKfSmooth F (ψf₀ s)) ∧
      (∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf₀ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) ∧
      (∀ (m₀ : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ m₀ * ‖ψf₀ ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t) ∧
      AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ₀ ∧
      (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ₀ g = (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf₀ ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, ψ₀ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b) ∧
      (∀ (y : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F),
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, AutomorphicForm.WindowedSiegel.IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ₀ (NumberField.AdelicLevel.diagOne y * k) =
            ((μ y : ℂˣ) : ℂ) * h₁ (Real.log (NumberField.TateGlobal.ideleNorm F y)) * φ₀ k) := by sorry
