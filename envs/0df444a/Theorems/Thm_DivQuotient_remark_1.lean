-- Prove2me | Theorems.Thm_DivQuotient_remark_1
-- name    : DivQuotient.remark_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:05.722181+00:00
-- url     : https://prove2.me/theorems/a1a85e2a-0091-48ea-8d98-ac5a9d696a33
-- title:
--   Remark 1 — [PC] is quasi-convexity of $\mathbf w\mapsto D(\mathbf w\odot\mathbf X)$
-- statement:
--   Let $D:\mathcal X^n\to\overline{\mathbb R}$ be any diversification index. Then $D$ satisfies portfolio convexity [PC] if and only if, for every $\mathbf X\in\mathcal X^n$, every $\lambda\in[0,1]$ and all $\mathbf w,\mathbf w'\in\Delta_n$,
--
--   $$
--   D\big((\lambda\mathbf w+(1-\lambda)\mathbf w')\odot\mathbf X\big)\le D(\mathbf w\odot\mathbf X)\vee D(\mathbf w'\odot\mathbf X).
--   $$
--
--   This is the form in which [PC] is verified for DQ in Theorem 2 and Proposition 1.
--
--   Differences from the source:
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, Remark 1, p.9

import Mathlib
import Definitions.Def_DivQuotient_Axioms

open MeasureTheory

namespace DivQuotient

/-- **Remark 1** (Han–Lin–Wang, arXiv:2206.13679v6, p.9): "Axiom [PC] is equivalent to
quasi-convexity of w ↦ D(w ⊙ X) for each X ∈ 𝒳ⁿ; that is, D((λw + (1 − λ)w′) ⊙ X) ⩽
D(w ⊙ X) ∨ D(w′ ⊙ X) for all λ ∈ [0, 1], w, w′ ∈ Δₙ and X ∈ 𝒳ⁿ."

For every map `D : 𝒳ⁿ → ℝ̄`, [PC] holds iff the displayed max-inequality holds. -/
theorem remark_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (D : (Fin n → Lp ℝ ⊤ P) → EReal) :
    AxPC D ↔
      ∀ (X : Fin n → Lp ℝ ⊤ P) (l : ℝ), l ∈ Set.Icc (0 : ℝ) 1 →
        ∀ w ∈ stdSimplex ℝ (Fin n), ∀ w' ∈ stdSimplex ℝ (Fin n),
          D (fun i => (l • w + (1 - l) • w') i • X i) ≤
            max (D (fun i => w i • X i)) (D (fun i => w' i • X i)) := by sorry

end DivQuotient
