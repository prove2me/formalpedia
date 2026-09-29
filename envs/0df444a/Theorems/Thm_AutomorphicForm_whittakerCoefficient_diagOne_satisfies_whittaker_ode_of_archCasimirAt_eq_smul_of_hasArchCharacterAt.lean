-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
-- name    : AutomorphicForm.whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/03f5927d-5b33-57dc-b1b0-90f5d95d6360
-- title:
--   Whittaker's equation for torus Whittaker coefficients at a real place
-- statement:
--   Let $K$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, $w$ a real infinite place of $K$, $n$ an integer, and $\lambda,\nu\in\mathbb{C}$ with $\nu^2=\tfrac14-\lambda$. Let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, left invariant under the unipotents $n(\beta)=\bigl(\begin{smallmatrix}1&\beta\\0&1\end{smallmatrix}\bigr)$ for $\beta\in K$, archimedean-smooth at $w$ in the sense that $e\mapsto\varphi(g\cdot\mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on $\{\det e\neq 0\}$ for every $g$, with all first and second derivatives $\mathrm{archDerivAt}$ along the three directions $H,E,F$ continuous, satisfying the Casimir eigenequation $-\bigl(\tfrac14 H^2\varphi-\tfrac12 H\varphi+EF\varphi\bigr)=\lambda\varphi$ and the predicate `HasArchCharacterAt₀` at $w$ for the character `archWeightCharAt hw n`, the $n$-th power of the weight-one character `archWeightOneℝ` transported along the isomorphism $K_w\cong\mathbb{R}$. Let $g_0$ have component $1$ at $w$ and $\varepsilon=\pm1$. Set $f(y)=W(g_0\cdot\mathrm{diag}(\varepsilon\sqrt y,1/\sqrt y)_w)$, where $W$ is the first Whittaker coefficient $\int\varphi(n(x)g)\psi_K(-x)\,d\nu(x)$ for the standard additive character and the carrier data `productionPinsOf` built from $D$, the levels $\mathrm{levelOne}\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the generators $\mathrm{heckeGen}$ and the box $\mathrm{adelicBox}$, whose additive measure is Haar measure conditioned on that box. Then $f$ and $f'$ are differentiable on $(0,\infty)$ and $y^2f''(y)+\bigl(\tfrac14-\nu^2+2\pi\varepsilon n\,y-4\pi^2y^2\bigr)f(y)=0$ for all $y>0$.
--
--   This is the archimedean Whittaker differential equation of weight $\varepsilon n$ for the restriction of the first Fourier–Whittaker coefficient to the diagonal torus at a real place; no automorphy of $\varphi$ beyond invariance under the rational unipotents is assumed. It feeds the subsequent analysis of Whittaker coefficients, namely the linear relations among torus values and the polynomial-growth bounds in the idele norm used in the cuspidal trichotomy.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (lam : ℂ) (ν : ℂ) (hν : ν ^ 2 = 1 / 4 - lam)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ)
    (hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (hφs : IsArchSmoothAt hw φ)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d φ))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' φ)))
    (hφΩ : archCasimirAt hw φ = lam • φ)
    (hφn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) φ)
    (g₀ : AdelicGL2 (𝓞 K) K) (hg₀ : archComponent K w (glArch (𝓞 K) K g₀) = 1)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    let f : ℝ → ℂ := fun y =>
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1
        (g₀ * archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]))
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * n : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by sorry
