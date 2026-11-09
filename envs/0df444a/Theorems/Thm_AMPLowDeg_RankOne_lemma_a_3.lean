-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_a_3
-- name    : AMPLowDeg.RankOne.lemma_a_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:59:38.070948+00:00
-- url     : https://prove2.me/theorems/f751d71e-3624-4a32-8335-83a994e21bbe
-- title:
--   Lemma A.3 — cumulants and independence
-- statement:
--   On a probability space, the following hold whenever the required mixed moments are finite.
--
--   1. If $a,b\ge1$ and the family $\{X_i\}_{i\in[a]}$ is independent of the family $\{Y_j\}_{j\in[b]}$, then
--   $$
--   \mathrm{Cum}(X_1,\dots,X_a,Y_1,\dots,Y_b)=0.
--   $$
--   2. If $\{X_i\}_{i\in[m]}$ is independent of $\{Y_i\}_{i\in[m]}$ ($m\ge1$), then
--   $$
--   \mathrm{Cum}(X_1+Y_1,\dots,X_m+Y_m)=\mathrm{Cum}(X_1,\dots,X_m)+\mathrm{Cum}(Y_1,\dots,Y_m).
--   $$
--   3. For jointly distributed $X_1,\dots,X_m$ ($m\ge1$) and any constant $c$,
--   $$
--   \mathrm{Cum}(X_1+c,X_2,\dots,X_m)=\mathrm{Cum}(X_1,\dots,X_m)+c\,\mathbf 1\{m=1\},\qquad \mathrm{Cum}(cX_1,X_2,\dots,X_m)=c\,\mathrm{Cum}(X_1,\dots,X_m).
--   $$
--
--   Part (1) is what makes the cumulants of disconnected graphs, or of graphs missing vertex $1$, vanish (Lemma 2.5(1)) and what kills mixed-vertex blocks in (6.6).
--
--   Differences from the source:
--
--   - reading: whenever the required mixed moments are finite; random variables → the variables are measurable and every product over a subset of the arguments is integrable (in (2): every product Π_{j∈A} X_j · Π_{j∈B} Y_j over disjoint A, B); reason: these are exactly the moments occurring in the partition formulas, including the mixed X/Y products obtained by expanding the arguments of (2)
--   - encoding: a list X₁, …, X_a, Y₁, …, Y_b; a list of n variables in (2), (3) → a family indexed by Fin a ⊕ Fin b; lists of length m ≥ 1 indexed by Fin m, the shifted or scaled variable being the first; reason: the cumulant (2.3) of an empty list is undefined, so the source's lists are nonempty; the length is renamed m to avoid a clash with the dimension n
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, pp. 21–22, Lemma A.3 (1)–(3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Cumulant

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- Lemma A.3, pp. 21–22 — cumulants and independence, whenever the mixed moments occurring in the
partition formula are finite:
(1) if `{X_i}_{i ∈ [a]}` is independent of `{Y_j}_{j ∈ [b]}` (`a, b ≥ 1`), then
`Cum(X₁, …, X_a, Y₁, …, Y_b) = 0`;
(2) if `{X_i}` is independent of `{Y_i}`, then `Cum(X₁ + Y₁, …, X_m + Y_m) = Cum(X) + Cum(Y)`;
(3) `Cum(X₁ + c, X₂, …, X_m) = Cum(X₁, …, X_m) + c·1{m = 1}` and
`Cum(cX₁, X₂, …, X_m) = c·Cum(X₁, …, X_m)` for every constant `c`. -/
theorem lemma_a_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (∀ (a b : ℕ), 1 ≤ a → 1 ≤ b → ∀ (X : Fin a → Ω → ℝ) (Y : Fin b → Ω → ℝ),
      (∀ i, Measurable (X i)) → (∀ j, Measurable (Y j)) →
      IndepFun (fun w i => X i w) (fun w j => Y j w) μ →
      (∀ A : Finset (Fin a ⊕ Fin b), Integrable (fun w => ∏ j ∈ A, Sum.elim X Y j w) μ) →
      cum μ (Sum.elim X Y) = 0) ∧
    (∀ m : ℕ, 1 ≤ m → ∀ (X Y : Fin m → Ω → ℝ),
      (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) →
      IndepFun (fun w i => X i w) (fun w i => Y i w) μ →
      (∀ A B : Finset (Fin m), Disjoint A B →
        Integrable (fun w => (∏ j ∈ A, X j w) * ∏ j ∈ B, Y j w) μ) →
      cum μ (fun i w => X i w + Y i w) = cum μ X + cum μ Y) ∧
    (∀ (m : ℕ) (hm : 1 ≤ m) (X : Fin m → Ω → ℝ) (c : ℝ),
      (∀ A : Finset (Fin m), Integrable (fun w => ∏ j ∈ A, X j w) μ) →
      cum μ (Function.update X ⟨0, hm⟩ (fun w => X ⟨0, hm⟩ w + c)) =
          cum μ X + c * (if m = 1 then 1 else 0) ∧
      cum μ (Function.update X ⟨0, hm⟩ (fun w => c * X ⟨0, hm⟩ w)) = c * cum μ X) := by sorry

end AMPLowDeg.RankOne
