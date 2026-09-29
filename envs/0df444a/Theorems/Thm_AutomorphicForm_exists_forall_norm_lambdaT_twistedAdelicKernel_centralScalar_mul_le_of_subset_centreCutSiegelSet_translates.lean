-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_lambdaT_twistedAdelicKernel_centralScalar_mul_le_of_subset_centreCutSiegelSet_translates
-- name    : AutomorphicForm.exists_forall_norm_lambdaT_twistedAdelicKernel_centralScalar_mul_le_of_subset_centreCutSiegelSet_translates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/3d8a40da-581f-5363-87e5-e4fa680d81b0
-- title:
--   Uniform bound for the truncated twisted GL₂ kernel on Siegel translates
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and an algebra over $K$, let $D$ be an idele Galois descent datum for $L/K$, that is, a monoid homomorphism from $L\simeq_{\mathrm{alg}[K]}L$ to the ring automorphisms of $\mathbb{A}_L=$ `AdeleRing (𝓞 L) L` which is continuous in each automorphism and compatible with the Galois action on principal adeles, and let $\sigma$ be a $K$-automorphism of $L$. Fix reals $c,u,d_1,d_2$ with $c>0$, a compact set $T_c\subseteq\mathrm{GL}_2(\mathbb{A}_L)$ and a set $S$ contained in the union of the right translates $\mathfrak S\,y$, $y\in T_c$, of the centre-cut Siegel set $\mathfrak S=$ `centreCutSiegelSet L c u d₁ d₂`, consisting of those $g$ whose finite part lies in `finiteIntegralGL2` and which at every infinite place $w$ satisfy $c\le$ `localHeight` of the $w$-component, `xWindowSq` of that component $\le u^2$, and `archDetNorm` $w\,g\in[d_1,d_2]$. Let $\varphi:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ be a factorizable test function, i.e. $\varphi(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ compactly supported and given by a $C^\infty$ function of the archimedean entries, and $f_{\mathrm{fin}}$ satisfying `IsFinTestFactor`. Then there is $T_0\in\mathbb{R}$ such that for every $T\ge T_0$ there is a constant $C$ with the following property: for every $x\in S$ and every idele $z\in\mathbb{A}_L^\times$, the value at $\mathrm{diag}(z,z)\,x$ of the truncation `lambdaT` — that is, the function minus the indicator of `highSet (adelicHeight L) T` times the constant term `constantTerm` along the unipotent family $t\mapsto\begin{pmatrix}1&t\\0&1\end{pmatrix}$, taken with respect to the probability measure obtained by conditioning the adelic additive Haar measure (for the Borel structure `adeleBorel`) on the adelic box `adelicBox L` — applied to the function $y\mapsto\sum_{\gamma\in\mathrm{GL}_2(L)}\varphi\bigl(x^{-1}\gamma\,\sigma_{\mathbb{A}}(y)\bigr)$, where $\sigma_{\mathbb A}$ is the entrywise action of $D(\sigma)$, has absolute value at most $C$.
--
--   This is the rank-one, twisted $\mathrm{GL}_2$ form of Arthur's bound for the truncated kernel, isolated as an estimate uniform in the point of the Siegel-set translate and in the central idele. It feeds the integrability statements for the truncated twisted kernel over a truncation domain, [`AutomorphicForm.exists_forall_le_integrableOn_mul_lambdaT_twistedAdelicKernel_canonicalTruncationDomain_prod`](thm.html#AutomorphicForm.exists_forall_le_integrableOn_mul_lambdaT_twistedAdelicKernel_canonicalTruncationDomain_prod) and [`AutomorphicForm.exists_forall_le_integrableOn_setIntegral_mul_lambdaT_adelicKernel_of_isTruncationDatum`](thm.html#AutomorphicForm.exists_forall_le_integrableOn_setIntegral_mul_lambdaT_adelicKernel_of_isTruncationDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_lambdaT_twistedAdelicKernel_centralScalar_mul_le_of_subset_centreCutSiegelSet_translates.lean

import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_TruncationOperator
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
    AutomorphicForm.exists_forall_norm_lambdaT_twistedAdelicKernel_centralScalar_mul_le_of_subset_centreCutSiegelSet_translates
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hS : S ⊆ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφf : AutomorphicForm.IsFactorizableTestFn L φ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∃ C : ℝ,
      ∀ x ∈ S, ∀ z : (AdeleRing (𝓞 L) L)ˣ,
        ‖@AutomorphicForm.lambdaT _ (adeleBorel (𝓞 L) L) _ _
            (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) T
            (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y)
            (AutomorphicForm.centralScalar (𝓞 L) L z * x)‖ ≤ C := by sorry
