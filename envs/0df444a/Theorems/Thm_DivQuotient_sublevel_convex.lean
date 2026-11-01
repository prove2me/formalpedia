-- Prove2me | Theorems.Thm_DivQuotient_sublevel_convex
-- name    : DivQuotient.sublevel_convex
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:27.98348+00:00
-- url     : https://prove2.me/theorems/9819f1a1-9893-4582-8a44-5d8f761ee4c2
-- title:
--   Proof of Theorem 2 — the sets $\{\mathbf w\in\Delta_n:r^{\mathbf X}_\beta(\mathbf w)\le0\}$ are convex
-- statement:
--   Let $I=(0,\bar\alpha)$, $\alpha\in I$, and let $\rho=(\rho_\beta)_{\beta\in I}$ be a decreasing class of real-valued risk measures, right-continuous in $\beta$ on $I$, such that $\mathrm{DQ}^\rho_\alpha$ satisfies [PC]. Then for every $\mathbf X\in\mathcal X^n$ and $\beta\in I$ the set
--
--   $$
--   \{\mathbf w\in\Delta_n:\ r^{\mathbf X}_\beta(\mathbf w)\le0\},\qquad r^{\mathbf X}_\beta(\mathbf w)=\rho_\beta\Big(\sum_{i=1}^nw_iX_i\Big)-\sum_{i=1}^n\rho_\alpha(w_iX_i),
--   $$
--
--   is convex.
--
--   This turns portfolio convexity of the index into a convexity property of each risk measure of the class, the first step towards their coherence.
--
--   Differences from the source:
--   - generalization: the class constructed in the proof of Theorem 1 (right-continuous by Remark EC.1) → any real-valued decreasing class, right-continuous in β on I, whose DQ satisfies [PC]; reason: the argument uses only these properties; the constructed class has them for coherent φ
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
--   - encoding: α* = inf{β ∈ I : …} with inf ∅ = ᾱ, ᾱ ∈ (0, ∞], DQ = α*/α, and a class (ρ_β)_{β∈I} → EReal infimum capped by ᾱ (min ᾱ (⨅ …)), divided in EReal by the real α > 0, and a map ℝ → Lp ℝ ⊤ P → … coerced to EReal; reason: the cap changes the value only on the empty set, where it gives ᾱ, and members outside I are never read; same values
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, proof of Theorem 2, p.36

import Mathlib
import Definitions.Def_DivQuotient_DQ
import Definitions.Def_DivQuotient_ProofObjects

open MeasureTheory Filter Topology

namespace DivQuotient

/-- **Proof of Theorem 2, sublevel convexity** (Han–Lin–Wang, arXiv:2206.13679v6, p.36):
"That is, the set {w ∈ Δₙ : r^X_β(w) ⩽ 0} is convex for any X ∈ 𝒳ⁿ and β ∈ I."

Let `ρ` be a real-valued decreasing class on `I = (0, ᾱ)`, right-continuous in `β` on `I`,
and `α ∈ I`, such that `DQ^ρ_α` satisfies [PC]. Then for all `X ∈ 𝒳ⁿ` and `β ∈ I` the set
`{w ∈ Δₙ : r^X_β(w) ≤ 0}` is convex, where `r^X_β(w) = ρ_β(∑ wᵢXᵢ) − ∑ ρ_α(wᵢXᵢ)`.

**Formalization Note.** The page derives `DQ(w ⊙ X) ≤ β` from `r^X_β(w) ≤ 0` under its
normalization `α = 1`; in general the bound is `β/α`, which changes nothing in the
statement. Right-continuity is `ContinuousWithinAt` on `(β, ∞)`. -/
theorem sublevel_convex {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (abar : EReal) (ρ : ℝ → Lp ℝ ⊤ P → ℝ) (α : ℝ) (hα : α ∈ IndexSet abar)
    (hdec : IsDecreasingClass abar (fun β X => (ρ β X : EReal)))
    (hrc : ∀ X : Lp ℝ ⊤ P, ∀ β ∈ IndexSet abar,
      ContinuousWithinAt (fun γ => ρ γ X) (Set.Ioi β) β)
    (hPC : AxPC (DQ (n := n) abar (fun β X => (ρ β X : EReal)) α))
    (X : Fin n → Lp ℝ ⊤ P) (β : ℝ) (hβ : β ∈ IndexSet abar) :
    Convex ℝ {w : Fin n → ℝ | w ∈ stdSimplex ℝ (Fin n) ∧ rFun ρ α β X w ≤ 0} := by sorry

end DivQuotient
