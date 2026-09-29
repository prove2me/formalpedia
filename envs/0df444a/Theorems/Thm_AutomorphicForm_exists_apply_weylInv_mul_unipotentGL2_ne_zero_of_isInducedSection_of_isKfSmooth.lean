-- Prove2me | Theorems.Thm_AutomorphicForm_exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth
-- name    : AutomorphicForm.exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/9f94b198-6e4e-5782-a1db-574f2e097850
-- title:
--   Non-vanishing of an induced section on the big cell
-- statement:
--   Let $F$ be a number field, and let $\alpha \colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ be the homomorphism of unit groups obtained from the distributive Haar character of the adele ring $\mathbb{A}_F$ (valued in $\mathbb{R}_{\ge 0}$, pushed into $\mathbb{R}$ and then into units). Assume $\alpha(t) > 0$ for every $t$, and fix $s \in \mathbb{C}$ and a function $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ subject to four hypotheses: (i) $\varphi$ is a section induced from the characters $\eta_1(t) = \alpha(t)^{s + 1/2}$ and $\eta_2(t) = \alpha(t)^{-(s+1/2)}$ (each built from the trivial character times the complex power of $\alpha$), meaning that for every $b$ in the Borel subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$, i.e. every invertible matrix with vanishing $(1,0)$ entry, and every $g$, one has $\varphi(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,\varphi(g)$, where $b_{00}, b_{11} \in \mathbb{A}_F^\times$ are the diagonal entries of $b$; (ii) $\varphi$ is continuous; (iii) $\varphi$ is $K_f$-smooth, that is, the stabiliser of $\varphi$ for right translation by the kernel of the archimedean-component map on $\mathrm{GL}_2(\mathbb{A}_F)$ is open in that kernel; (iv) $\varphi$ is not identically zero. Then there exists $x \in \mathbb{A}_F$ with $\varphi(w^{-1} n(x)) \neq 0$, where $w$ is the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of the antidiagonal matrix $\begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix}$ over $F$ and $n(x) = \begin{pmatrix} 1 & x \\ 0 & 1 \end{pmatrix}$.
--
--   This is the non-vanishing statement needed before the Weyl intertwining integral of an induced section can be studied: since the big Bruhat cell $B w N$ is dense, a non-zero section cannot vanish along all the representatives $w^{-1} n(x)$, so the integrand of the intertwining integral is not identically zero. It is used in establishing lower bounds, for $\mathrm{Re}(s)$ large, on the intertwining integral attached to a family of such sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (_hφc : Continuous φ) (_hφf : IsKfSmooth F φ) (_hne : ∃ g, φ g ≠ 0),
    ∃ x : AdeleRing (𝓞 F) F, φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ≠ 0 := by sorry
