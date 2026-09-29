-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection
-- name    : AutomorphicForm.exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/d08c150d-0d85-5c84-9406-830c5b0219fd
-- title:
--   Induced sections on GL₂(A_F) are bounded by H^{Res+1/2}
-- statement:
--   Let $F$ be a number field. Write $\alpha$ for the homomorphism $(\mathbb{A}_F)^\times \to \mathbb{R}^\times$ obtained from the distributive Haar character of the adele ring $\mathbb{A}_F$ (its values in $\mathbb{R}_{\ge 0}$ viewed in $\mathbb{R}$ and promoted to units), and assume $\alpha(x)>0$ for every $x$; this positivity is an explicit hypothesis $h\alpha$. Let $\mu,\nu \colon (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be characters that are unitary in the sense that $\|\mu(x)\| = \|\nu(x)\| = 1$ for all $x$, let $s \in \mathbb{C}$, and let $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous and an induced section for the pair $\bigl(\mu\cdot\alpha^{\,s+1/2},\ \nu\cdot\alpha^{-(s+1/2)}\bigr)$, where $\alpha^{z}(x) := \alpha(x)^{z}$ is the complex power of the positive real $\alpha(x)$; that is, for every $b$ in the adelic Borel subgroup (the matrices in $\mathrm{GL}_2(\mathbb{A}_F)$ whose $(1,0)$ entry vanishes) and every $g$, $$\varphi(bg) = \mu(b_{00})\,\alpha(b_{00})^{s+1/2}\,\nu(b_{11})\,\alpha(b_{11})^{-(s+1/2)}\,\varphi(g).$$ Then there exists a real constant $C$ with $\|\varphi(g)\| \le C \cdot \mathrm{adelicHeight}_F(g)^{\operatorname{Re}(s)+1/2}$ for all $g \in \mathrm{GL}_2(\mathbb{A}_F)$, the height being the product of the archimedean height of the archimedean part of $g$ and the finite height of its finite part.
--
--   This is the standard majorisation of a flat section of an adelic principal series of $\mathrm{GL}_2$ by a power of the adelic height, obtained from the Iwasawa decomposition $g = bk$ together with boundedness of $|\varphi|$ on the maximal compact subgroup. It is used in the convergence and analyticity arguments for Eisenstein series and Rankin–Selberg integrals, notably by the statements on analyticity of $s$-part integrals and on continuity of the Weyl intertwining integral for $\operatorname{Re}(s) > 1/2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection
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
    ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 F) F, ‖φ g‖ ≤ C * adelicHeight F g ^ (s.re + 1 / 2) := by sorry
