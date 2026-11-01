-- Prove2me | Theorems.Thm_DivQuotient_dq_mem_Icc
-- name    : DivQuotient.dq_mem_Icc
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:19.677542+00:00
-- url     : https://prove2.me/theorems/b84c10da-848a-4c1b-b097-9925926623d4
-- title:
--   Proof of Proposition 1 — DQ takes values in $[0,1]$ when $\rho_\alpha$ is subadditive
-- statement:
--   Let $n\ge1$, $I=(0,\bar\alpha)$, $\alpha\in I$, and let $\rho=(\rho_\beta)_{\beta\in I}$ be a class of real-valued risk measures with $\rho_\alpha$ subadditive. Then for every $\mathbf X\in\mathcal X^n$,
--
--   $$
--   0\le\mathrm{DQ}^\rho_\alpha(\mathbf X)\le1.
--   $$
--
--   In particular the convention $\inf\varnothing=\bar\alpha$ never applies to such a DQ, and it never takes the value $\infty$.
--
--   Differences from the source:
--   - generalization: ρ a decreasing class of sub-linear risk measures → any real-valued class with ρ_α subadditive; reason: the bound uses only subadditivity of ρ_α; a decreasing sub-linear class satisfies this
--   - encoding: n is a fixed positive integer (Notation, p.4) → hypothesis 0 < n; reason: the paper's standing assumption; at n = 0 the statement fails or is vacuous
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
--   - encoding: α* = inf{β ∈ I : …} with inf ∅ = ᾱ, ᾱ ∈ (0, ∞], DQ = α*/α, and a class (ρ_β)_{β∈I} → EReal infimum capped by ᾱ (min ᾱ (⨅ …)), divided in EReal by the real α > 0, and a map ℝ → Lp ℝ ⊤ P → … coerced to EReal; reason: the cap changes the value only on the empty set, where it gives ᾱ, and members outside I are never read; same values
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, proof of Proposition 1, p.44

import Mathlib
import Definitions.Def_DivQuotient_DQ

open MeasureTheory

namespace DivQuotient

/-- **DQ takes values in [0, 1]** (Han–Lin–Wang, arXiv:2206.13679v6, proof of Proposition 1,
p.44): "The subadditivity of ρ_α implies that DQ^ρ_α takes value in [0, 1]."

For any real-valued class `ρ` indexed by `I = (0, ᾱ)`, any `α ∈ I` with `ρ_α` subadditive,
and every `X ∈ 𝒳ⁿ`, `0 ≤ DQ^ρ_α(X) ≤ 1`.

**Formalization Note.** `n ≥ 1` is the paper's standing assumption (p.4, "a fixed positive
integer"). At `n = 0` the claim needs `ρ_α(0) ≤ 0`, which subadditivity alone does not give
(`ρ_α ≡ 1` is subadditive). -/
theorem dq_mem_Icc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (abar : EReal) (ρ : ℝ → Lp ℝ ⊤ P → ℝ) (α : ℝ) (hα : α ∈ IndexSet abar)
    (hsub : IsSubadditive (ρ α)) (X : Fin n → Lp ℝ ⊤ P) :
    DQ abar (fun β X => (ρ β X : EReal)) α X ∈ Set.Icc (0 : EReal) 1 := by sorry

end DivQuotient
