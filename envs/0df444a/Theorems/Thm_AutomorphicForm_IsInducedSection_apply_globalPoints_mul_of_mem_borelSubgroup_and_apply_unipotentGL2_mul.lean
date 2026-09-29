-- Prove2me | Theorems.Thm_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul
-- name    : AutomorphicForm.IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/4e20eeef-9292-5581-88af-b367d2b8932a
-- title:
--   Induced sections are left invariant under B(F) and N(A_F)
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, and let $\alpha\colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ be the character obtained from the distributive Haar character `distribHaarChar` of $\mathbb{A}_F$ by pushing its $\mathbb{R}_{\ge 0}$-values into $\mathbb{R}$ and taking values in units. The assertion is: for every proof $h\alpha$ that $\alpha(t) > 0$ for all $t$, all monoid homomorphisms $\mu, \nu\colon \mathbb{A}_F^\times \to \mathbb{C}^\times$ which are idele class characters (i.e. trivial on the image of $F^\times$ under $F \to \mathbb{A}_F$), every $s \in \mathbb{C}$ and every $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ satisfying the induced-section identity $\varphi(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,\varphi(g)$ for all $g$ and all $b \in \mathrm{GL}_2(\mathbb{A}_F)$ with $b_{10} = 0$, where $\eta_1 = \mu\cdot\alpha^{s+1/2}$ and $\eta_2 = \nu\cdot\alpha^{-(s+1/2)}$ (complex powers of the positive real values of $\alpha$), two invariance statements hold: first, $\varphi(\iota(b)g) = \varphi(g)$ for every $b \in \mathrm{GL}_2(F)$ with $b_{10} = 0$, where $\iota$ is the entrywise map $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A}_F)$, and for every $g$; second, $\varphi(n(u)g) = \varphi(g)$ for all $u \in \mathbb{A}_F$ and all $g$, where $n(u) = \begin{pmatrix} 1 & u \\ 0 & 1\end{pmatrix}$.
--
--   This is the well-definedness statement underlying the $\mathrm{GL}_2$ Eisenstein series $E(g,s) = \sum_{\gamma \in B(F)\backslash \mathrm{GL}_2(F)} \varphi(\gamma g)$ attached to a section of the principal series induced from $(\mu|\cdot|^{s+1/2}, \nu|\cdot|^{-(s+1/2)})$: each summand depends only on the coset $B(F)\gamma$, and the section is invariant under the full adelic unipotent radical. It is used in the construction and analytic continuation of adelic Eisenstein series and in the Maass–Selberg and pseudo-Eisenstein computations built on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHeight AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ),
    (∀ b : Matrix.GeneralLinearGroup (Fin 2) F, b ∈ borelSubgroup F →
      ∀ g : AdelicGL2 (𝓞 F) F, φ (globalPoints (𝓞 F) F b * g) = φ g) ∧
    (∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 u * g) = φ g) := by sorry
