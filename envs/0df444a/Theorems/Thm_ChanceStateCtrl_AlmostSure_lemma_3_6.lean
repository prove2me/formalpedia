-- Prove2me | Theorems.Thm_ChanceStateCtrl_AlmostSure_lemma_3_6
-- name    : ChanceStateCtrl.AlmostSure.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:56.8179+00:00
-- url     : https://prove2.me/theorems/172b3e53-246a-41f4-8105-f23ee4aea3ca
-- title:
--   Lemma 3.6, p. 20 — a.s. unique state y(·, ω) ∈ H¹₀(D) ∩ C(D̄), y ∈ L∞_P(Ω, C(D̄)), and the bound (52)
-- statement:
--   Let $D\subseteq\mathbb R^d$, $d\in\{1,2,3\}$, be open, bounded and of class S, and let $(\Omega,\mathcal F,\mathbb P)$ be a probability space. For $u\in L^2(D)$ and $\tilde f\in L^\infty_{\mathbb P}(\Omega,L^2(D))$ consider the random elliptic problem
--   $$-\Delta y(x,\omega)=u(x)+\tilde f(x,\omega)\ \ (x\in D),\qquad y(x,\omega)=0\ \ (x\in\partial D).$$
--   Then:
--
--   1. for $\mathbb P$-almost every $\omega$ this problem has a weak solution $y(\cdot,\omega)\in H^1_0(D)\cap\mathcal C(\bar D)$, and it is unique on $\bar D$;
--   2. these solutions define an element $y\in L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D))$;
--   3. there is a constant $C>0$, independent of $u$ and $\tilde f$, such that
--   $$\|y\|_{L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D))}\le C\bigl(\|u\|_{L^2(D)}+\|\tilde f\|_{L^\infty_{\mathbb P}(\Omega,L^2(D))}\bigr).\qquad(52)$$
--
--   The lemma makes the control-to-state operator $\mathcal S$ of problem (51) well defined and bounded.
--
--   **Formalization Note** Item 3 is stated for every $Y\in L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D))$ whose value at $\mathbb P$-a.e. $\omega$ is the weak solution for that $\omega$; the constant is chosen before $u$, $\tilde f$ and $Y$. The probability space is fixed before the constant.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 20, Lemma 3.6, (52)

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory

namespace ChanceStateCtrl.AlmostSure

/-- Lemma 3.6 (p. 20). Under Assumption 3.5: (a) for every `u ∈ L²(D)`, `f̃ ∈ L∞_P(Ω, L²(D))` and
`P`-a.e. `ω`, (51b)–(51c) has a unique solution `y(·, ω) ∈ H¹₀(D) ∩ C(D̄)` (unique on `D̄`);
(b) these solutions form an element of `L∞_P(Ω, C(D̄))`; (c) there is `C > 0`, independent of `u`
and `f̃`, with `‖y‖_{L∞_P(Ω, C(D̄))} ≤ C (‖u‖_{L²(D)} + ‖f̃‖_{L∞_P(Ω, L²(D))})` (52). -/
theorem lemma_3_6 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    -- (a) existence and uniqueness, `P`-a.s.
    (∀ (u : ChanceStateCtrl.PDE.L2 D) (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P), ∀ᵐ ω ∂P,
        ∃ y, ChanceStateCtrl.PDE.IsDirichletSol D (⇑(u + ftil ω)) y ∧
          ∀ y', ChanceStateCtrl.PDE.IsDirichletSol D (⇑(u + ftil ω)) y' → ∀ x ∈ closure D, y' x = y x) ∧
    -- (b) `y ∈ L∞_P(Ω, C(D̄))`
    (∀ (u : ChanceStateCtrl.PDE.L2 D) (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P), ∃ Y : Linf D P, ∀ᵐ ω ∂P,
        ∃ y, ChanceStateCtrl.PDE.IsDirichletSol D (⇑(u + ftil ω)) y ∧ ∀ x : closure D, Y ω x = y x) ∧
    -- (c) the bound (52)
    (∃ C : ℝ, 0 < C ∧ ∀ (u : ChanceStateCtrl.PDE.L2 D) (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (Y : Linf D P),
        (∀ᵐ ω ∂P, ∃ y, ChanceStateCtrl.PDE.IsDirichletSol D (⇑(u + ftil ω)) y ∧ ∀ x : closure D, Y ω x = y x) →
        ‖Y‖ ≤ C * (‖u‖ + ‖ftil‖)) := by sorry

end ChanceStateCtrl.AlmostSure
