-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection
-- name    : AutomorphicForm.exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/25292b12-cefb-5ca4-a06e-2efd25ae4036
-- title:
--   Induced sections on GL₂(A_F) grow like H^{σ+1/2}
-- statement:
--   Let $F$ be a number field. Write $\alpha$ for the monoid homomorphism from the idele group $(\mathbb{A}_F)^\times$ to $\mathbb{R}^\times$ obtained from the distributive Haar character of $(\mathbb{A}_F)^\times$ acting on $\mathbb{A}_F$, composed with the coercion $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passed to units. Assume $\alpha$ takes strictly positive real values, and let $\mu,\nu:(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ be homomorphisms that are unitary in the sense that $\|\mu(x)\|=\|\nu(x)\|=1$ for all ideles $x$, let $s\in\mathbb{C}$ and let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and an induced section for the pair $(\mu\cdot\alpha^{s+1/2},\ \nu\cdot\alpha^{-(s+1/2)})$, i.e. for every $b$ in the subgroup of matrices with vanishing $(1,0)$ entry and every $g$ one has $\varphi(bg)=\mu(b_{00})\alpha(b_{00})^{s+1/2}\,\nu(b_{11})\alpha(b_{11})^{-(s+1/2)}\varphi(g)$, where $b_{00},b_{11}$ are the diagonal entries viewed as ideles. Then there exists a real $C\ge 0$ with $\|\varphi(g)\|\le C\cdot H(g)^{\mathrm{Re}(s)+1/2}$ for all $g\in\mathrm{GL}_2(\mathbb{A}_F)$, where $H$ is the adelic height, the product of the archimedean height of the infinite component with the finite height of the finite component.
--
--   This is the standard elementary growth estimate for sections of the adelic principal series of $\mathrm{GL}_2$: such a section is dominated by the spherical vector $H^{\sigma+1/2}$. It is the basic majorant used in the convergence and continuity arguments for pseudo-Eisenstein series and their constant terms, and is cited by the results on continuity of pseudo-Eisenstein series and on bounds over the canonical truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_AdelicHeight
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHeight AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : AdelicGL2 (𝓞 F) F,
      ‖φ g‖ ≤ C * adelicHeight F g ^ (s.re + 1 / 2) := by sorry
