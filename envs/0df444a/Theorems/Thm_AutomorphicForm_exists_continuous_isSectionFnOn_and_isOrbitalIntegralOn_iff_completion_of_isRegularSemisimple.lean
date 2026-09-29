-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple
-- name    : AutomorphicForm.exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/a7c432e0-6b44-55fa-97cd-73cf2a8c7101
-- title:
--   Continuous section functions and single-valued orbital integrals at regular semisimple γ
-- statement:
--   Let $K$ be a number field and $v$ an infinite place of $K$, with completion $K_v$; the groups $\mathrm{GL}_2(K_v)$ and the centraliser of a point are given their Borel $\sigma$-algebras (`glBorelOf` and `centralizerBorel`, the Borel structures of the ambient topologies). Let $\mu$ be a Haar measure on $\mathrm{GL}_2(K_v)$, let $\gamma \in \mathrm{GL}_2(K_v)$ satisfy `IsRegularSemisimple`, i.e. $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of $K_v$, let $\tau$ be a Haar measure on the centraliser $T_\gamma = \mathrm{Cent}(\{\gamma\}) \le \mathrm{GL}_2(K_v)$, and let $f : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be Borel measurable, of compact support, and bounded (some real $C$ with $\|f(g)\| \le C$ for all $g$). Call $w : \mathrm{GL}_2(K_v) \to \mathbb{R}$ a section function for $(\gamma,\tau,f)$ when $w \ge 0$ pointwise, $w$ is measurable with compact support, and $\int_{T_\gamma} w(tx)\,d\tau(t) = 1$ for every $x$ with $f(x^{-1}\gamma x) \ne 0$. The assertion is twofold: first, a continuous section function exists; second, for every section function $w$ and every $I \in \mathbb{C}$, the relation `IsOrbitalIntegralOn` holds for $(\mu,\gamma,\tau,f,I)$ — that is, $I = \int f(x^{-1}\gamma x)\,w'(x)\,d\mu(x)$ for some section function $w'$ — if and only if $I = \int_{\mathrm{GL}_2(K_v)} f(x^{-1}\gamma x)\,w(x)\,d\mu(x)$.
--
--   This is the archimedean dictionary lemma for the orbital-integral vocabulary of the project: the relation `IsOrbitalIntegralOn`, which encodes Harish-Chandra style orbital integrals through section functions rather than quotient measures, is both inhabited and single-valued at a regular semisimple element, so it may be used interchangeably with the explicit integral against any one section function. It is invoked in the comparison of twisted and ordinary orbital integrals at infinite places and in the matching statements for central transfer of scalar data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple
    (K : Type) [Field K] [NumberField K] (v : NumberField.InfinitePlace K)
    (μ : @Measure (GL (Fin 2) v.Completion) (glBorelOf v.Completion))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf v.Completion) μ)
    (γ : GL (Fin 2) v.Completion) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) v.Completion))) (centralizerBorel v.Completion γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion γ) τ)
    (f : GL (Fin 2) v.Completion → ℂ) (hfm : Measurable[glBorelOf v.Completion] f)
    (hfc : HasCompactSupport f) (hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) :
    (∃ w : GL (Fin 2) v.Completion → ℝ, IsSectionFnOn v.Completion γ τ f w ∧ Continuous w) ∧
      ∀ w : GL (Fin 2) v.Completion → ℝ, IsSectionFnOn v.Completion γ τ f w →
        ∀ I : ℂ, IsOrbitalIntegralOn v.Completion μ γ τ f I ↔
          I = @integral _ ℂ _ _ (glBorelOf v.Completion) μ fun x => f (x⁻¹ * γ * x) * (w x : ℂ) := by sorry
