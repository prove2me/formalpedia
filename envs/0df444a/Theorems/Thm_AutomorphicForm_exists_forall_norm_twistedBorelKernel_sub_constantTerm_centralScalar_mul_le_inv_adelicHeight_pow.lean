-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_twistedBorelKernel_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
-- name    : AutomorphicForm.exists_forall_norm_twistedBorelKernel_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/6643a871-fd08-577c-8cfd-f78178fe1b9b
-- title:
--   Cuspidal decay of the twisted Borel kernel minus its constant term
-- statement:
--   Let $K$ be a field and $L$ a number field equipped with a $K$-algebra structure, let $D$ be an idele Galois descent datum for $L/K$ (a monoid homomorphism from $L\simeq_{\mathrm{alg}[K]}L$ to the ring automorphisms of $\mathbb{A}_L$, compatible with $\mathrm{alg}$-maps of principal adeles and continuous), and let $\sigma$ be a $K$-automorphism of $L$, acting entrywise on $\mathrm{GL}_2(\mathbb{A}_L)$ through [`AutomorphicForm.sigmaAdelicAct`](def/AutomorphicForm_SigmaAdelicAction.html#L14). Let $c,u,d_1,d_2$ be reals with $c>0$, let $T_c\subseteq\mathrm{GL}_2(\mathbb{A}_L)$ be compact, and let $S$ be contained in the union over $y\in T_c$ of the right translates by $y$ of the centre-cut Siegel set `centreCutSiegelSet L c u d₁ d₂` (finite part in `finiteIntegralGL2`; at every infinite place $w$ the local height of the archimedean component is at least $c$, its squared window is at most $u^2$, and `archDetNorm` lies in $[d_1,d_2]$). Let $\varphi:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ be factorizable: $\varphi(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ where $f_\infty$ is a compactly supported function given by a $C^\infty$ function of the archimedean matrix entries and $f_{\mathrm{fin}}$ satisfies `IsFinTestFactor`. Then there is $T_1\in\mathbb{R}$ such that for every $N\in\mathbb{N}$ there is $C\in\mathbb{R}$ with the following property: for all $x\in S$ with `adelicHeight L x` $>T_1$ and all ideles $z\in\mathbb{A}_L^\times$, the norm of the difference between the finitely supported sum $\sum_{\gamma}\varphi\bigl(x^{-1}\gamma\,\sigma_{\mathbb{A}}(c(z)x)\bigr)$, over the $\gamma\in\mathrm{GL}_2(L)$ with vanishing lower-left entry viewed in $\mathrm{GL}_2(\mathbb{A}_L)$, and the value at $c(z)x$ of the constant term of $y\mapsto\sum_{\gamma}\varphi\bigl(x^{-1}\gamma\,\sigma_{\mathbb{A}}(y)\bigr)$ along the upper unipotent subgroup $t\mapsto n(t)$, taken with respect to adelic Haar measure conditioned on the adelic box (Borel $\sigma$-algebra `adeleBorel`), is at most $C\cdot(\mathrm{adelicHeight}\,x)^{-N}$.
--
--   This is the unipotent, Poisson-summation estimate of the rank-one trace formula for $\mathrm{GL}_2$, in the form twisted by $\sigma$ and with constants uniform in the central variable $z$: high in the cusp the twisted Borel kernel differs from its constant term along the unipotent radical by a quantity decaying faster than any power of the adelic height. It is the analytic input to [`AutomorphicForm.exists_forall_norm_lambdaT_twistedAdelicKernel_centralScalar_mul_le_of_subset_centreCutSiegelSet_translates`](thm.html#AutomorphicForm.exists_forall_norm_lambdaT_twistedAdelicKernel_centralScalar_mul_le_of_subset_centreCutSiegelSet_translates), which bounds the truncated twisted kernel on translates of centre-cut Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_twistedBorelKernel_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

theorem
    AutomorphicForm.exists_forall_norm_twistedBorelKernel_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hS : S ⊆ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφf : AutomorphicForm.IsFactorizableTestFn L φ) :
    ∃ T₁ : ℝ, ∀ N : ℕ, ∃ C : ℝ,
      ∀ x ∈ S, T₁ < NumberField.AdelicHeight.adelicHeight L x → ∀ z : (AdeleRing (𝓞 L) L)ˣ,
        ‖(∑ᶠ γ ∈ (AutomorphicForm.borelSubgroup L : Set (Matrix.GeneralLinearGroup (Fin 2) L)),
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
          - @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
              (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (fun y => ∑ᶠ γ ∈ (AutomorphicForm.borelSubgroup L : Set (Matrix.GeneralLinearGroup (Fin 2) L)),
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ y))
              (AutomorphicForm.centralScalar (𝓞 L) L z * x)‖ ≤
          C * (NumberField.AdelicHeight.adelicHeight L x)⁻¹ ^ N := by sorry
