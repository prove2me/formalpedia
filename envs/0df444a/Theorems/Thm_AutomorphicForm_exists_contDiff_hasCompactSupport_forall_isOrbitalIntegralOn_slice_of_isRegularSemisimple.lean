-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_isOrbitalIntegralOn_slice_of_isRegularSemisimple
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isOrbitalIntegralOn_slice_of_isRegularSemisimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/0d275904-83ff-5b03-a382-92bb03e9ed2e
-- title:
--   Orbital integrals of a smooth family depend smoothly on the parameter
-- statement:
--   Let $\mathbb{k}$ be an `RCLike` field (so $\mathbb{R}$ or $\mathbb{C}$), let $P$ be a normed real vector space, let $\mu$ be a Haar measure on $\mathrm{GL}_2(\mathbb{k})$ for the Borel $\sigma$-algebra `glBorelOf`, let $\gamma \in \mathrm{GL}_2(\mathbb{k})$ be regular semisimple in the sense that $(\operatorname{tr}\gamma)^2 - 4\det\gamma$ is a unit, and let $\tau$ be a Haar measure on the centraliser $Z$ of $\{\gamma\}$ in $\mathrm{GL}_2(\mathbb{k})$, for the Borel $\sigma$-algebra `centralizerBorel`. Let $\Phi \colon (\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{k}) \times P \to \mathbb{C}$ be $C^\infty$ over $\mathbb{R}$, of compact support, with $\operatorname{tsupport}\Phi$ contained in the set of pairs whose matrix coordinate has unit determinant. The assertion is that there is a function $g \colon P \to \mathbb{C}$, again $C^\infty$ over $\mathbb{R}$ and of compact support, such that for every $p \in P$, writing $f_p(x) = \Phi(x, p)$ for $x \in \mathrm{GL}_2(\mathbb{k})$ (entries read off the underlying matrix): first, $g(p)$ is an orbital-integral value for $f_p$, i.e. there is $w \colon \mathrm{GL}_2(\mathbb{k}) \to \mathbb{R}$ which is non-negative, measurable and compactly supported, satisfies $\int_{Z} w(tx)\,d\tau(t) = 1$ for every $x$ with $f_p(x^{-1}\gamma x) \neq 0$, and for which $g(p) = \int f_p(x^{-1}\gamma x)\,w(x)\,d\mu(x)$; and second, any complex number $I$ admitting such a section function $w$ and representation equals $g(p)$.
--
--   This is the archimedean orbital integral of $\mathrm{GL}_2$ taken with a parameter: one smooth compactly supported function of all matrix entries and of a point of a normed space, rather than a product of test functions, so that a single archimedean place can be treated at a time. The uniqueness half rests on [`AutomorphicForm.IsOrbitalIntegralOn.unique_of_isRegularSemisimple`](thm.html#AutomorphicForm.IsOrbitalIntegralOn.unique_of_isRegularSemisimple), and the statement is used by the two vanishing results [`AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_complex_eq_zero`](thm.html#AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_complex_eq_zero) and its real counterpart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_isOrbitalIntegralOn_slice_of_isRegularSemisimple.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isOrbitalIntegralOn_slice_of_isRegularSemisimple
    (𝕜 : Type) [RCLike 𝕜] (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (μ : @Measure (GL (Fin 2) 𝕜) (glBorelOf 𝕜)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf 𝕜) μ)
    (γ : GL (Fin 2) 𝕜) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) 𝕜))) (centralizerBorel 𝕜 γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel 𝕜 γ) τ)
    (Φ : (Fin 2 → Fin 2 → 𝕜) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ∃ g : P → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      ∀ p : P,
        IsOrbitalIntegralOn 𝕜 μ γ τ (fun x => Φ (Matrix.of.symm (x : Matrix (Fin 2) (Fin 2) 𝕜), p)) (g p) ∧
        ∀ I : ℂ, IsOrbitalIntegralOn 𝕜 μ γ τ (fun x => Φ (Matrix.of.symm (x : Matrix (Fin 2) (Fin 2) 𝕜), p)) I →
          I = g p := by sorry
