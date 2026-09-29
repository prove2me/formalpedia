-- Prove2me | Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt
-- name    : AutomorphicForm.exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/75b84556-4d62-5da2-9f56-ddeb7347d6b2
-- title:
--   Base-independent multiplier for torus Whittaker coefficients at a complex place
-- statement:
--   Let $K$ be a number field, let $D$ be a subset of $GL_2(\mathbb{A}_K)$, and let $P$ denote the carrier data `productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, whose central subgroup is all of $\mathbb{A}_K^\times$, whose level subgroups are the intersections of the principal level subgroups with the kernel of the archimedean projection, whose local generators are the Hecke elements at the finite places, and whose additive measure $\nu$ is the adelic additive Haar measure conditioned on the box `adelicBox K` (infinite box times integral finite adeles). Let $\xi : \mathbb{A}_K^\times \to \mathbb{C}^\times$ be a character, $w_0 \in \mathbb{R}$, and assume $\lVert\xi(z)\rVert = \mathrm{ideleNorm}_K(z)^{w_0}$ for all ideles $z$, where the idele norm is the modulus of the distributive Haar character. Let $w$ be a complex infinite place of $K$, let $n \in \mathbb{N}$, and let $x_0,\dots,x_n : GL_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy: $x_p(\mathrm{diag}(z,z)\,g) = \xi(z)\,x_p(g)$ for all ideles $z$ and all $g$, and `HasCircleWeightAt hw ((n : ℤ) - 2 * p) (x p)`, i.e. $x_p(g\cdot \iota_w(\zeta)) = \zeta^{\,n-2p}\,x_p(g)$ for every $\zeta \in \mathbb{C}^\times$ of modulus $1$, where $\iota_w$ is the circle element at $w$. Then there are functions $\mu_p : K_w \to \mathbb{C}$, $0 \le p \le n$, with $\lVert \mu_p(t)\rVert = \lVert t\rVert^{\,m_w w_0/2}$ for all $t \in K_w$ ($m_w =$ `w.mult`), such that for every idele $b$ with trivial finite component, every $p$, and every idele $a$ with trivial finite component agreeing with $b$ at all infinite places other than $w$, the Whittaker coefficient of $x_p$ for the standard additive character [`NumberField.StandardAddChar.stdAddChar K`](def/NumberField_AdelicTraceFin.html#L198) at $\alpha = 1$, namely $\int \, x_p(u(y)\,g)\,\psi(-y)\,d\nu(y)$, satisfies $$W(x_p)(\mathrm{diag}(a,1)) = \mu_p(a_w)\, W(x_p)\bigl(\mathrm{diag}(b\cdot \mathrm{archUnitHom}_w(b_w)^{-1},1)\cdot \mathrm{archComplexGLAt}_{hw}(\mathrm{diag}(e^{u},e^{-u}))\bigr),$$ with $u = \tfrac12\log\lVert a_w\rVert$ and $\mathrm{archComplexGLAt}$ the embedding of $GL_2(\mathbb{C})$ into $GL_2(\mathbb{A}_K)$ at the complex place $w$; here $b\cdot \mathrm{archUnitHom}_w(b_w)^{-1}$ is $b$ with its $w$-component replaced by $1$. The multiplier $\mu_p$ depends on neither $b$ nor the rest of $a$.
--
--   This is the exact central-character twist comparing the Whittaker function of a weight string on the diagonal torus of $GL_2(\mathbb{A}_K)$ with its value on the split torus of $GL_2(\mathbb{C})$ at a complex place, the multiplier being independent of the base idele. It feeds the analysis of Whittaker functions along $SU(2)$-strings in [`AutomorphicForm.exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String`](thm.html#AutomorphicForm.exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleBox
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem AutomorphicForm.exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p)) :
    ∃ μ : Fin (n + 1) → w.Completion → ℂ,
      (∀ (p : Fin (n + 1)) (t : w.Completion), ‖μ p t‖ = ‖t‖ ^ ((w.mult : ℝ) * w₀ / 2)) ∧
      ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
        ∀ (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a) =
            μ p (((a : AdeleRing (𝓞 K) K)).1 w) *
              whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne (b * (NumberField.TateGlobal.archUnitHom w (NumberField.AdeleRing.infiniteUnitsComponent (𝓞 K) K w b))⁻¹) *
                archComplexGLAt hw (splitTorusGL2Complex ((Real.log ‖((a : AdeleRing (𝓞 K) K)).1 w‖ / 2 : ℝ) : ℂ))) := by sorry
