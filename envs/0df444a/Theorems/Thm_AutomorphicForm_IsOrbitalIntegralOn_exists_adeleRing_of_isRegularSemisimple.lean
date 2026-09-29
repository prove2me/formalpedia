-- Prove2me | Theorems.Thm_AutomorphicForm_IsOrbitalIntegralOn_exists_adeleRing_of_isRegularSemisimple
-- name    : AutomorphicForm.IsOrbitalIntegralOn.exists_adeleRing_of_isRegularSemisimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/48b13292-6068-527e-9973-cd9418337dcc
-- title:
--   Existence of adelic orbital integrals at regular semisimple γ
-- statement:
--   Let $K$ be a number field, write $G = \mathrm{GL}_2(\mathbb{A}_K)$ for the general linear group of $2\times 2$ matrices over the adele ring of $K$, equipped with its Borel $\sigma$-algebra, and let $\mu$ be an arbitrary measure on $G$ (no invariance or regularity is assumed). Let $\gamma \in G$ be regular semisimple in the sense of the project, that is, its discriminant $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of $\mathbb{A}_K$; let $\tau$ be a Haar measure on the centraliser $G_\gamma$ of $\{\gamma\}$ in $G$, again with its Borel $\sigma$-algebra; and let $f : G \to \mathbb{C}$ be compactly supported (no continuity or measurability is assumed). The conclusion asserts the existence of a complex number $I$ which is an orbital integral of $f$ at $\gamma$ relative to $\mu$ and $\tau$ in the section-function sense: there is a weight $w : G \to \mathbb{R}$ that is non-negative, measurable and compactly supported, satisfies $\int_{G_\gamma} w(tx)\,\mathrm{d}\tau(t) = 1$ for every $x \in G$ with $f(x^{-1}\gamma x) \neq 0$, and for which $I = \int_G f(x^{-1}\gamma x)\, w(x)\, \mathrm{d}\mu(x)$.
--
--   This is the adelic existence statement for orbital integrals of compactly supported functions at regular semisimple elements of $\mathrm{GL}_2(\mathbb{A}_K)$, in the normalisation where the quotient measure on the orbit is realised through a section function on $G$ cutting the centraliser fibres to total mass $1$. It supplies the existence half of the comparison of twisted and ordinary orbital integrals used in the base-change matching of covolumes and orbital integrals for matching elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsOrbitalIntegralOn_exists_adeleRing_of_isRegularSemisimple.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.IsOrbitalIntegralOn.exists_adeleRing_of_isRegularSemisimple
    (K : Type) [Field K] [NumberField K]
    (μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (γ : AutomorphicForm.AdelicGL2 (𝓞 K) K) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    [τ.IsHaarMeasure]
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : HasCompactSupport f) :
    ∃ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ γ τ f I := by sorry
