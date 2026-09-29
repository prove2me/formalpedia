-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/0bcd590d-9bbd-5324-84f0-81025d88eab3
-- title:
--   Archimedean weighted orbital germ identity at split classes
-- statement:
--   Let $K$ be a number field and $f_\infty:\mathrm{GL}_2(K_\infty)\to\mathbb C$ an archimedean test factor, i.e. $f_\infty$ has compact support and $f_\infty(g)=\Phi$ of the matrix of mixed-space images of the entries of $g$ for some $\Phi$ smooth of class $C^\infty$ over $\mathbb R$; let $\tau_0$ be a measure on $K_\infty\times K_\infty$, with $K_\infty$ carrying its Borel structure. Then there exist $B$ and families $C_w,E_w$ indexed by the infinite places $w$ of $K$, all functions $(\mathrm{Fin}\,2\to$ mixed space of $K)\to\mathbb C$, all $C^\infty$ over $\mathbb R$ and compactly supported, such that: at any point where $B$ or some $C_w$ or $E_w$ is nonzero both coordinates come from units of $K_\infty$; there is a compact set $Ca$ of pairs of units of $K_\infty$ with $\operatorname{tsupport}B\cup\bigcup_w(\operatorname{tsupport}C_w\cup\operatorname{tsupport}E_w)$ contained in the image of $Ca$ under the coordinatewise mixed-space identification; and for all units $a,t$ of $K_\infty$ with $\gamma=\mathrm{diag}(a,at)$ regular semisimple (meaning $\operatorname{tr}(\gamma)^2-4\det(\gamma)$ is a unit), every Haar measure $\tau$ on the centraliser of $\gamma$ in $\mathrm{GL}_2(K_\infty)$ whose pushforward along $x\mapsto(x_{00},x_{11})$ is $\tau_0$, and all $J,I\in\mathbb C$ such that, for the Haar measure `archHaarK` on $\mathrm{GL}_2(K_\infty)$ and some functions satisfying the section predicate `IsSectionFnOn` for $\gamma,\tau,f_\infty$, $J=\int f_\infty(x^{-1}\gamma x)\,\mathrm{wt}(x)\,s(x)$ with weight $\mathrm{wt}(y)=-\log H_\infty(y)-\log H_\infty(w_0y)$, where $H_\infty$ is the archimedean height and $w_0$ the archimedean component of the global Weyl element, and $I=\int f_\infty(x^{-1}\gamma x)\,s'(x)$, one has
--   $$\nu(t)J=-2\Big(\sum_w m_w\log\|1-t_w\|\Big)\,\nu(t)I+B(\iota t,\iota a)+\sum_{w\ \mathrm{real}}\|1-t_w\|\,C_w(\iota t,\iota a)+\sum_{w\ \mathrm{complex}}\|1-t_w\|^2\log\|1-t_w\|\,E_w(\iota t,\iota a),$$
--   where $t_w$ is the component of $t$ at $w$, $m_w$ its multiplicity, $\nu(t)=\prod_w(\|1-t_w\|/\sqrt{\|t_w\|})^{m_w}$, and $\iota$ is the mixed-space identification.
--
--   This is the archimedean germ expansion of the weighted orbital integral along the split torus: the singular behaviour of $J$ as $t\to1$ is exactly $-2\sum_w m_w\log\|1-t_w\|$ times the plain orbital integral $I$, up to smooth compactly supported remainders with real and complex place corrections of sizes $\|1-t_w\|$ and $\|1-t_w\|^2\log\|1-t_w\|$. It feeds the comparison of twisted and untwisted weighted orbital integrals used on the archimedean side of the trace formula in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex
    (K : Type) [Field K] [NumberField K]
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (τ₀ : Measure (InfiniteAdeleRing K × InfiniteAdeleRing K)) :
    ∃ (B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ)
      (C E : NumberField.InfinitePlace K → (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) B ∧ (∀ w, ContDiff ℝ (⊤ : ℕ∞) (C w)) ∧ (∀ w, ContDiff ℝ (⊤ : ℕ∞) (E w)) ∧
      HasCompactSupport B ∧ (∀ w, HasCompactSupport (C w)) ∧ (∀ w, HasCompactSupport (E w)) ∧
      (∀ p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K, (B p ≠ 0 ∨ ∃ w, C w p ≠ 0 ∨ E w p ≠ 0) →
        IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧ IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧

      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport B ∪ ⋃ w, (tsupport (C w) ∪ tsupport (E w)), ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) →
      ∀ (τ : Measure (Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
        τ.IsHaarMeasure →
        Measure.map
            (fun x : Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
              ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
                ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
                InfiniteAdeleRing K × InfiniteAdeleRing K))
            τ = τ₀ →
      ∀ J I : ℂ, AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
          (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
            -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
              - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
                  (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y)))
          (diagUnits2 a (a * t)) τ fa J →
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
          (diagUnits2 a (a * t)) τ fa I →
        ((∏ w : NumberField.InfinitePlace K,
              (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ /
                  Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖) ^ w.mult : ℝ) : ℂ) * J =
          -2 * ((∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) *
              Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            (((∏ w : NumberField.InfinitePlace K,
              (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ /
                  Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖) ^ w.mult : ℝ) : ℂ) * I) +
          B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) :
                ℂ) * C w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                  Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ :
                  ℝ) : ℂ) *
                E w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by sorry
