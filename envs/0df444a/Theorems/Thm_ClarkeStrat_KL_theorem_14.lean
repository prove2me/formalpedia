-- Prove2me | Theorems.Thm_ClarkeStrat_KL_theorem_14
-- name    : ClarkeStrat.KL.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:50.774343+00:00
-- url     : https://prove2.me/theorems/4b0746d5-0d84-4da2-9ba9-cacef77f93b4
-- title:
--   Theorem 14 (nonsmooth Kurdyka–Łojasiewicz inequality), p. 568 — ‖x*‖ ≥ 1/ψ′(|f(x)|) for x* ∈ ∂°f(x), 0 < |f(x)| ≤ χ(‖x‖)
-- statement:
--   Let $\mathcal O$ be an o-minimal structure on $(\mathbb R,+,\cdot)$ and let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be a lower semicontinuous function definable in $\mathcal O$. Then there exist $\rho>0$, a strictly increasing continuous definable function $\psi:[0,\rho)\to\mathbb R$ which is $C^1$ on $(0,\rho)$ with $\psi(0)=0$, and a continuous definable function $\chi:\mathbb R_+\to(0,\rho)$, such that
--   $$\|x^*\|\ge\frac{1}{\psi'(|f(x)|)} \tag{22}$$
--   whenever $0<|f(x)|\le\chi(\|x\|)$ and $x^*\in\partial^\circ f(x)$, the Clarke subdifferential of $f$ at $x$.
--
--   This is a nonsmooth Kurdyka–Łojasiewicz inequality: it holds globally in $x$, relative to the value $0$, for every lower semicontinuous definable function, and bounds every Clarke subgradient (not only the one of least norm) from below.
--
--   **Formalization Note** (22) is stated multiplied out, as $\psi'(|f(x)|)\,\|x^*\|\ge1$; this is equivalent where $\psi'>0$ and avoids the Lean convention $1/0=0$. The paper prints $\psi:[0,\rho)\to(0,+\infty)$ together with $\psi(0)=0$; positivity of $\psi$ on $(0,\rho)$ follows from strict monotonicity and $\psi(0)=0$. Since $x^*\in\partial^\circ f(x)$ forces $f(x)<+\infty$, $|f(x)|$ is a real number. $f$ is assumed never equal to $-\infty$; definability of $\psi$ and $\chi$ is part of the conclusion.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), p. 568, Theorem 14, (22)

import Mathlib
import Definitions.Def_ClarkeStrat_KL_Setting

open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared

namespace ClarkeStrat.KL

/-- Theorem 14 (nonsmooth Kurdyka–Łojasiewicz inequality), p. 568. Let `f : ℝⁿ → ℝ ∪ {+∞}` be a
lower semicontinuous function definable in an o-minimal structure. There are `ρ > 0`, a strictly
increasing continuous definable `ψ : [0, ρ) → ℝ`, `C¹` on `(0, ρ)` with `ψ(0) = 0`, and a continuous
definable `χ : ℝ₊ → (0, ρ)` such that `ψ′(|f(x)|) ‖x*‖ ≥ 1` (that is, (22): `‖x*‖ ≥ 1/ψ′(|f(x)|)`)
whenever `0 < |f(x)| ≤ χ(‖x‖)` and `x* ∈ ∂°f(x)`. -/
theorem theorem_14 (O : OMinimalStructure) {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (hlsc : LowerSemicontinuous f) (hdef : graphSet f ∈ O.O (n + 1)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ψ χ : ℝ → ℝ,
      StrictMonoOn ψ (Set.Ico 0 ρ) ∧ ContinuousOn ψ (Set.Ico 0 ρ) ∧
      DefinableOn1 O (Set.Ico 0 ρ) ψ ∧ ContDiffOn ℝ 1 ψ (Set.Ioo 0 ρ) ∧ ψ 0 = 0 ∧
      ContinuousOn χ (Set.Ici 0) ∧ DefinableOn1 O (Set.Ici 0) χ ∧
      (∀ s, 0 ≤ s → χ s ∈ Set.Ioo 0 ρ) ∧
      ∀ x, ∀ v ∈ ClarkeSubdiff f x, 0 < |(f x).toReal| → |(f x).toReal| ≤ χ ‖x‖ →
        1 ≤ deriv ψ |(f x).toReal| * ‖v‖ := by sorry

end ClarkeStrat.KL
