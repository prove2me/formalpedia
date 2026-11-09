-- Prove2me | Theorems.Thm_ElimAgree_theorem_3_1
-- name    : ElimAgree.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:27:51.168192+00:00
-- url     : https://prove2.me/theorems/2ceaf503-8506-4e90-a6af-1447ed9df245
-- title:
--   Theorem 3.1 — logarithmic-deficit transfer (all three clauses)
-- statement:
--   Let $\alpha,\beta$ be finite input sets and $F:\alpha\times\beta\to\{0,1\}^k$. For each $z\in\{0,1\}^k$ let $\nu_z$ be a law supported on $F^{-1}(z)$, and let $\lambda=\nu_{z_0}$ for one fixed $z_0$. Suppose that for some $\eta>0$, every rectangle $R$ and every $z$,
--   $$\nu_z(R)\ge\lambda(R)-\eta\,J_\lambda(R).\tag{3.1}$$
--   Let $0<g\le1$. Then:
--   1. every public-coin protocol with common output and error at most $(1-g)2^{-k}$ on every input has cost
--   $$c\ge\frac{2g}{\eta\ln2}-\frac{2}{e\ln2},$$
--   even when the parties may disagree;
--   2. $c\ge 2g/(\eta\ln 2)$ when the output is determined by the transcript;
--   3. a protocol with that error in which, after the coins are fixed, the output at each leaf is a function of one designated party's input taking at most $M$ values on that leaf satisfies $c+\log_2M\ge2g/(\eta\ln2)$.
--
--   No product structure, balance or operator norm is assumed.
--
--   Differences from the source:
--   - generalization: F(X, Y) = (f_1(x_1, y_1), …, f_k(x_k, y_k)) on k-tuples of inputs → an arbitrary F : α → β → {0,1}^k on finite α, β; reason: the proof never uses the coordinate structure; the source's F is the instance α = Π X_i, β = Π Y_i
--   - reading: g with the paper's standing convention 0 < g ≤ 1 (§1, p.1) → hypotheses 0 < g and g ≤ 1; reason: Theorem 3.1 states no range for g; this is the convention of the paper
--   - reading: the third clause without a restated error bound → the same pointwise error (1 − g)2^{−k}; reason: the clause continues the sentence about protocols with that error, and its proof uses it
--   - encoding: log M (all logarithms base two, §2, p.6) → Real.logb 2 M; reason: Lean convention; same values
--   - encoding: public-coin protocols that may also use private coins; cost in bits → PMF over deterministic protocol trees (private coins absorbed); cost = maximal depth over the support; reason: fixing all coins leaves a deterministic tree, and every distribution over trees is a public-coin protocol
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem 3.1, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_ElimAgree_ComLabel
import Definitions.Def_ElimAgree_IsLaw
import Definitions.Def_ElimAgree_deficit

namespace ElimAgree

/-- Theorem 3.1 (Logarithmic-deficit transfer), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.7. Let `F : α → β → {0,1}^k`. For
each `z ∈ {0, 1}^k` let `ν_z` be a law supported on `F^{−1}(z)`, and let `λ = ν_{z₀}` for one
fixed `z₀`. Suppose that for some `η > 0`, every rectangle `R` and every `z`,
`ν_z(R) ≥ λ(R) − η J_λ(R)` (3.1). Then, for `0 < g ≤ 1`:
1. every public-coin protocol with common output and pointwise error at most `(1 − g)2^{−k}`
   has cost `c ≥ 2g/(η ln 2) − 2/(e ln 2)`, even when the parties may disagree;
2. `c ≥ 2g/(η ln 2)` when the output is determined by the transcript;
3. a protocol in which, after the coins are fixed, the output at each leaf is a function of one
   designated party's input taking at most `M` values on that leaf satisfies
   `c + log₂ M ≥ 2g/(η ln 2)`.

**Formalization Note.** Protocols are distributions over deterministic trees (`OneOfManyCC.Protocol`); cost
is the maximal depth over the support; error is pointwise on every `(x, y) ∈ α × β`. -/
theorem theorem_3_1 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {k : ℕ} (F : α → β → (Fin k → Bool)) (ν : (Fin k → Bool) → α × β → ℝ)
    (hν : ∀ z, IsLaw (ν z)) (hsupp : ∀ z (p : α × β), ν z p ≠ 0 → F p.1 p.2 = z)
    (z₀ : Fin k → Bool) (η : ℝ) (hη : 0 < η)
    (h31 : ∀ (z : Fin k → Bool) (A : Finset α) (B : Finset β),
      lawRect (ν z) A B ≥ lawRect (ν z₀) A B - η * deficit (ν z₀) A B)
    (g : ℝ) (hg : 0 < g) (hg1 : g ≤ 1) :
    (∀ (c : ℕ) (μ : PMF (OneOfManyCC.Protocol α β (ComLabel α β (Fin k → Bool)))), CostLE μ c →
      (∀ x y, comErr F μ x y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) →
      2 * g / (η * Real.log 2) - 2 / (Real.exp 1 * Real.log 2) ≤ c) ∧
    (∀ (c : ℕ) (μ : PMF (OneOfManyCC.Protocol α β (Fin k → Bool))), CostLE μ c →
      (∀ x y, tdErr F μ x y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) →
      2 * g / (η * Real.log 2) ≤ c) ∧
    (∀ (c M : ℕ) (μ : PMF (OneOfManyCC.Protocol α β ((α → Fin k → Bool) ⊕ (β → Fin k → Bool)))),
      CostLE μ c → (∀ T ∈ μ.support, LeafValuesLE M T Set.univ Set.univ) →
      (∀ x y, desErr F μ x y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) →
      2 * g / (η * Real.log 2) ≤ c + Real.logb 2 M) := by sorry

end ElimAgree
