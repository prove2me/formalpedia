-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isSectionFnOn_adeleRing_of_isRegularSemisimple
-- name    : AutomorphicForm.exists_isSectionFnOn_adeleRing_of_isRegularSemisimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/a96d5da0-e3b8-5522-95e4-aa565532fc7a
-- title:
--   Section functions for regular semisimple adelic GL₂ orbital integrals
-- statement:
--   Let $K$ be a number field and let $G = GL_2(\mathbb{A}_K)$ be the general linear group of $2\times 2$ matrices over the adele ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K`, with its Borel $\sigma$-algebra. Let $\gamma \in G$ be regular semisimple in the sense of the project's predicate [`AutomorphicForm.IsRegularSemisimple`](def/AutomorphicForm_LocalOrbitalBase.html#L402), namely that the discriminant $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ of the characteristic polynomial of $\gamma$ is a unit of $\mathbb{A}_K$. Let $T = Z_G(\gamma)$ be the centralizer of the singleton $\{\gamma\}$ in $G$, equipped with its Borel $\sigma$-algebra, and let $\tau$ be a Haar measure on $T$. Finally let $f \colon G \to \mathbb{C}$ have compact support. Then there exists $w \colon G \to \mathbb{R}$ which is a section function for these data, i.e. $w(x) \ge 0$ for all $x$, $w$ is Borel measurable, $w$ has compact support, and for every $x \in G$ with $f(x^{-1}\gamma x) \neq 0$ one has $\int_T w(tx)\,d\tau(t) = 1$.
--
--   This is the standard device that makes the adelic orbital integral $\int_{Z_G(\gamma)\backslash G} f(x^{-1}\gamma x)\,dx$ at a regular semisimple element meaningful without quotient measures, by inserting a compactly supported weight $w$ whose $T$-integral is $1$ on the support of $x \mapsto f(x^{-1}\gamma x)$; its existence rests on the properness of the orbit map modulo the centralizer. It feeds the construction of orbital integrals ([`AutomorphicForm.IsOrbitalIntegralOn.exists_adeleRing_of_isRegularSemisimple`](thm.html#AutomorphicForm.IsOrbitalIntegralOn.exists_adeleRing_of_isRegularSemisimple)) and, through these, the unfolding of the elliptic terms in the comparison of trace formulas for $GL_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isSectionFnOn_adeleRing_of_isRegularSemisimple.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.exists_isSectionFnOn_adeleRing_of_isRegularSemisimple
    (K : Type) [Field K] [NumberField K]
    (γ : AutomorphicForm.AdelicGL2 (𝓞 K) K) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    [τ.IsHaarMeasure]
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : HasCompactSupport f) :
    ∃ w : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ,
      AutomorphicForm.IsSectionFnOn (AdeleRing (𝓞 K) K) γ τ f w := by sorry
