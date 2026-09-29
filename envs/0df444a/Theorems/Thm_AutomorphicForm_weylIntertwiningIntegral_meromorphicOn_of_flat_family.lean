-- Prove2me | Theorems.Thm_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_flat_family
-- name    : AutomorphicForm.weylIntertwiningIntegral_meromorphicOn_of_flat_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/41b2f1fb-0887-5982-b152-8cb1ede7923d
-- title:
--   Meromorphic continuation of the Weyl intertwining integral, flat families
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}_F$ and idele group $\mathbb{A}_F^\times$, and let $\alpha\colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ be the character obtained from the distributive Haar character of $\mathbb{A}_F$ by pushing its $\mathbb{R}_{\ge 0}$-values into $\mathbb{R}$ and passing to units; assume $\alpha(x) > 0$ for all $x$. Let $\mu, \nu\colon \mathbb{A}_F^\times \to \mathbb{C}^\times$ be characters that are unitary, in the sense that $|\mu(x)| = |\nu(x)| = 1$ for every idele $x$, and trivial on the principal ideles, i.e. $\mu(u) = \nu(u) = 1$ for $u \in F^\times$ embedded diagonally. Let $\varphi\colon \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family of functions such that: for each $s$, $\varphi_s$ is an induced section for the pair $(\mu\,\alpha^{s+1/2},\ \nu\,\alpha^{-(s+1/2)})$, that is $\varphi_s(bg) = \mu\alpha^{s+1/2}(b_1)\,\nu\alpha^{-(s+1/2)}(b_2)\,\varphi_s(g)$ for every $b$ in the adelic Borel subgroup with diagonal entries $b_1, b_2$ and every $g$; each $\varphi_s$ is archimedean $K$-finite at every infinite place of $F$ and is a smooth vector for right translation by the finite adelic $\mathrm{GL}_2$ subgroup; the map $(s,g) \mapsto \varphi_s(g)$ is jointly continuous; and the family is flat, meaning $\varphi_s(k) = \varphi_{s'}(k)$ for all $s, s'$ whenever the finite part of $k$ lies in $\mathrm{GL}_2$ of the integral finite adeles and, at every infinite place $w$, the component of $k$ is a row isometry (its determinant has norm $1$ and the associated map preserves $|x|^2 + |y|^2$). Then, for every fixed $g \in \mathrm{GL}_2(\mathbb{A}_F)$, with the Borel measurable structure on $\mathbb{A}_F$ and its additive Haar measure, there exists $M'\colon \mathbb{C} \to \mathbb{C}$ meromorphic on all of $\mathbb{C}$ such that $M'(s) = \int_{\mathbb{A}_F} \varphi_s(w^{-1} n(x) g)\, dx$ for every $s$ with $\operatorname{Re} s > 1/2$, where $w$ is the adelic Weyl element and $n(x)$ the upper unipotent matrix with entry $x$.
--
--   This is the meromorphic continuation of the global intertwining operator $M(s)$ attached to the principal series of $\mathrm{GL}_2$ over a number field, in the form where the section family is assumed flat on the maximal compact subgroup rather than merely holomorphic in $s$; the integral itself converges only in the right half-plane $\operatorname{Re} s > 1/2$, and the assertion is the existence of a meromorphic function on $\mathbb{C}$ agreeing with it there, for each fixed $g$. It feeds the corresponding statement for general families of induced sections, which in turn underlies the analytic continuation of Eisenstein series used in the trace-formula and base-change input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_flat_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

theorem AutomorphicForm.weylIntertwiningIntegral_meromorphicOn_of_flat_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    ∃ M' : ℂ → ℂ, MeromorphicOn M' Set.univ
      ∧ ∀ s : ℂ, 1 / 2 < s.re → M' s
        = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g := by sorry
