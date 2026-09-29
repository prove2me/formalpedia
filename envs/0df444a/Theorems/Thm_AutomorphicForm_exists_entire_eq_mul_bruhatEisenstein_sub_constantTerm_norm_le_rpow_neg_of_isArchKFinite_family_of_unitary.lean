-- Prove2me | Theorems.Thm_AutomorphicForm_exists_entire_eq_mul_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family_of_unitary
-- name    : AutomorphicForm.exists_entire_eq_mul_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family_of_unitary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/76448e97-89cc-54ea-b421-f63aa4c4242d
-- title:
--   Entire normalisation of the non-constant term of an Eisenstein family
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ obtained from the module `distribHaarChar` of the adele ring by passing from $\mathbb{R}_{\ge 0}$ to $\mathbb{R}^\times$, assumed pointwise positive (hypothesis $h\alpha$). Let $\mu,\nu\colon(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ be characters that are unitary, $|\mu(x)|=|\nu(x)|=1$ for all ideles $x$, and trivial on the image of $F^\times$. Let $\varphi\colon\mathbb{C}\to\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that: for each $s$, $\varphi_s(bg)=\eta_1(b_{00})\eta_2(b_{11})\varphi_s(g)$ for $b$ in the adelic Borel subgroup (lower-left entry zero), where $\eta_1=\mu\,\alpha^{s+1/2}$ and $\eta_2=\nu\,\alpha^{-(s+1/2)}$; for each $s$ and each infinite place $w$ the right translates of $\varphi_s$ under the subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ coming from the row-isometries of $\mathrm{GL}_2(F_w)$ span a finite-dimensional space; for each $s$ the stabiliser of $\varphi_s$ under right translation by the kernel of the archimedean projection is open; $(s,g)\mapsto\varphi_s(g)$ is continuous; $s\mapsto\varphi_s(g)$ is entire for each $g$; and for each infinite place $w$ there is one finite-dimensional subspace $W$ of functions on that row-isometry subgroup containing $k\mapsto\varphi_s(gk)$ for all $s$ and $g$. Put $E_s(h)=\varphi_s(h)+\sum_{\xi\in F}\varphi_s(w\,n(\xi)h)$ with $w$ the image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\xi)$ the upper unipotent matrix with entry $\xi$, and $\mathrm{hgt}(b)=\alpha(b_{00})/\alpha(b_{11})$ for $b$ in the adelic Borel subgroup. Then there are $Z\colon\mathbb{C}\to\mathbb{C}$ and $V\colon\mathbb{C}\to\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ such that $Z$ is holomorphic and nowhere zero on $\{\mathrm{Re}\,s>1\}$; $s\mapsto V_s(h)$ is entire for every $h$; for $\mathrm{Re}\,s>1$ one has $V_s(h)=Z(s)\bigl(E_s(h)-\int E_s(n(t)h)\,dt\bigr)$, the integral being against the adelic additive Haar measure conditioned on the adelic box; and for all compact $C\subseteq\mathbb{C}$, compact $\Omega\subseteq\mathrm{GL}_2(\mathbb{A}_F)$, $c'>0$ and $N\in\mathbb{N}$ there is $M\in\mathbb{R}$ with $\|V_s(b\omega)\|\le M\,\mathrm{hgt}(b)^{-N}$ for all $s\in C$, all $b$ in the adelic Borel subgroup with $\mathrm{hgt}(b)\ge c'$, and all $\omega\in\Omega$.
--
--   This is the statement that, after multiplication by a holomorphic zero-free normalising factor on $\{\mathrm{Re}\,s>1\}$ (an Euler product built from the local Whittaker data), the difference between a degenerate Eisenstein series attached to two unitary idele class characters of $\mathrm{GL}_2$ over $F$ and its constant term along the adelic unipotent subgroup extends to an entire function of $s$ which decays faster than any power of the height on Siegel sets, locally uniformly in $s$ and uniformly in the compact part. It is used by [`AutomorphicForm.norm_sub_constantTerm_le_mul_rpow_neg_of_axis_continuation_family`](thm.html#AutomorphicForm.norm_sub_constantTerm_le_mul_rpow_neg_of_axis_continuation_family), which transfers the decay estimate to the continued family on a vertical axis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_entire_eq_mul_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family_of_unitary.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.exists_entire_eq_mul_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family_of_unitary
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W),
    letI := adeleBorel (𝓞 F) F
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∃ (Z : ℂ → ℂ) (V : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      DifferentiableOn ℂ Z {s : ℂ | 1 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → Z s ≠ 0) ∧
      (∀ h : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s => V s h)) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 < s.re →
        V s h = Z s * (E s h -
          constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => unipotentGL2 t) (E s) h)) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
        IsCompact C → IsCompact Ω → 0 < c' →
        ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
          ω ∈ Ω → c' ≤ hgt b →
            ‖V s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤ M * (hgt b) ^ (-(N : ℝ))) := by sorry
