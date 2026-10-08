-- Prove2me | Theorems.Thm_AffinePSD_Existence_proposition_5_3
-- name    : AffinePSD.Existence.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:14.665772+00:00
-- url     : https://prove2.me/theorems/3da91579-fb68-403c-b7f3-36aebb073519
-- title:
--   Proposition 5.3 — global unique R_+ × S_d^{++}-valued solutions of the Riccati equations, analytic in (t, u)
-- statement:
--   Let $(\alpha,b,\beta^{ij},c,\gamma,m,\mu)$ be an admissible parameter set, with $F,R$ as in (2.16)–(2.17). Then:
--   1. for every $u\in S_d^{++}$ there is a unique pair $(\varphi(\cdot,u),\psi(\cdot,u))$ on $[0,\infty)$ with values in $\mathbb R_+\times S_d^{++}$ solving
--   $$\partial_t\varphi(t,u)=F(\psi(t,u)),\ \ \varphi(0,u)=0,\qquad\partial_t\psi(t,u)=R(\psi(t,u)),\ \ \psi(0,u)=u;$$
--   2. these solutions can be chosen jointly so that $\varphi(t,u)$ and $\psi(t,u)$ are real analytic in $(t,u)\in\mathbb R_+\times S_d^{++}$;
--   3. the integrands defining $F(u)$ and $R(u)$ are integrable for every $u\in S_d^+$.
--
--   Proposition 5.9 uses these solutions to compute the Laplace transform of any solution of the martingale problem, which yields uniqueness.
--
--   **Formalization Note** "Global" means defined for all $t\ge0$; derivatives at $t=0$ are one-sided, and uniqueness is among $\mathbb R_+\times S_d^{++}$-valued solutions on $[0,\infty)$. Joint analyticity is analyticity within the set $[0,\infty)\times\{y:\operatorname{sym}(y)\succ0\}$ of $(t,y)\mapsto\psi(t,\operatorname{sym}y)$, and the same for $\varphi$. Item 3 rules out Lean's convention that a non-integrable integral is $0$. The proof uses Lemma 3.3 (proved in the companion mission on necessity).
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Proposition 5.3, p. 39

import Mathlib
import Definitions.Def_AffinePSD_Existence_Params

namespace AffinePSD.Existence

/-- Proposition 5.3 (arXiv:0910.0137v3, §5.1, p. 39): for every `u ∈ S_d^{++}` there is a unique
global `R_+ × S_d^{++}`-valued solution `(φ, ψ)` of (2.14)–(2.15), and `φ(t,u)`, `ψ(t,u)` are
analytic in `(t, u) ∈ R_+ × S_d^{++}`.
Formalization Note: a solution from `u` is a pair `f : ℝ → ℝ`, `g : ℝ → M_d` with `f 0 = 0`,
`g 0 = u`, and for every `t ≥ 0`: `f t ≥ 0`, `g t ≻ 0`, `f'(t) = F(g t)`, `g'(t) = R(g t)`
(one-sided at `t = 0`); uniqueness is among such pairs on `t ≥ 0`. Joint analyticity on
`R_+ × S_d^{++}` is `AnalyticOn` (analyticity within the set, so one-sided at `t = 0`) of
`(t, y) ↦ ψ(t, (y + y^⊤)/2)` on `[0, ∞) × {y | (y + y^⊤)/2 ≻ 0}`, and likewise for `φ`. The
leading conjunct `RiccatiIntegrable` (the integrands of (2.16)–(2.17) are integrable) guards against
Lean's junk value of a non-integrable Bochner integral; it is stronger than the page and true. -/
theorem proposition_5_3 {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) (hP : AffinePSD.Necessity.Admissible χ P) :
    RiccatiIntegrable χ P ∧
    (∀ u, PD u → ∃ (f : ℝ → ℝ) (g : ℝ → Mat d),
      (f 0 = 0 ∧ g 0 = u ∧ ∀ t, 0 ≤ t → 0 ≤ f t ∧ PD (g t) ∧
        HasDerivWithinAt f (AffinePSD.Necessity.Fpar P (g t)) (Set.Ici 0) t ∧
        HasDerivWithinAt g (AffinePSD.Necessity.Rpar χ P (g t)) (Set.Ici 0) t) ∧
      ∀ (f' : ℝ → ℝ) (g' : ℝ → Mat d),
        (f' 0 = 0 ∧ g' 0 = u ∧ ∀ t, 0 ≤ t → 0 ≤ f' t ∧ PD (g' t) ∧
          HasDerivWithinAt f' (AffinePSD.Necessity.Fpar P (g' t)) (Set.Ici 0) t ∧
          HasDerivWithinAt g' (AffinePSD.Necessity.Rpar χ P (g' t)) (Set.Ici 0) t) →
        ∀ t, 0 ≤ t → f' t = f t ∧ g' t = g t) ∧
    ∃ (φ : ℝ → Mat d → ℝ) (ψ : ℝ → Mat d → Mat d),
      (∀ u, PD u → φ 0 u = 0 ∧ ψ 0 u = u ∧ ∀ t, 0 ≤ t → 0 ≤ φ t u ∧ PD (ψ t u) ∧
        HasDerivWithinAt (fun s => φ s u) (AffinePSD.Necessity.Fpar P (ψ t u)) (Set.Ici 0) t ∧
        HasDerivWithinAt (fun s => ψ s u) (AffinePSD.Necessity.Rpar χ P (ψ t u)) (Set.Ici 0) t) ∧
      AnalyticOn ℝ (fun q : ℝ × Mat d => φ q.1 (sym q.2)) (Set.Ici 0 ×ˢ {y | PD (sym y)}) ∧
      AnalyticOn ℝ (fun q : ℝ × Mat d => ψ q.1 (sym q.2)) (Set.Ici 0 ×ˢ {y | PD (sym y)}) := by sorry

end AffinePSD.Existence
