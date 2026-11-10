-- Prove2me | Theorems.Thm_EvasivePatterns_lemma_5_3
-- name    : EvasivePatterns.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:13.862965+00:00
-- url     : https://prove2.me/theorems/3048bbe6-3b26-4444-964c-1f32e18105a7
-- title:
--   Lemma 5.3 — a primitive Wronskian isolates a simple root $\alpha$
-- statement:
--   Let $Q \in \mathbb Z[z]$ have constant term $1$, nonzero coefficients in $\{\pm1\}$, rigid support and full autocorrelation norm $\|QQ^*\|_1 = |\mathrm{supp}\, Q|^2$. If $\mathrm{cont}(W_Q) = 1$, then $Q$ has a simple complex root $\alpha$ such that
--   $$
--   Q(\beta) = 0,\ \ \beta/\alpha \text{ a root of unity} \quad\Longrightarrow\quad \beta = \alpha .
--   $$
--
--   Such an isolated root is what prevents periodic cancellation in the coefficients of $1/Q$.
--
--   Differences from the source:
--   - encoding: β/α a root of unity → (β/α)ⁿ = 1 for some n > 0; reason: same content
--   - encoding: rigid support (every homometric finite set is a translate of S or of its reflection) → Rigid, quantified over nonempty finite integer sets; reason: the notions differ only for a one-point support, i.e. Q = 1, where W_Q = 0 and cont(W_Q) = 0 ≠ 1; no instance changes
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Lemma 5.3, display (10), p.8 (PDF p.9), lines 252–254

import Mathlib
import Definitions.Def_EvasivePatterns_Rigid
import Definitions.Def_EvasivePatterns_l1Norm
import Definitions.Def_EvasivePatterns_recipWronskian

namespace EvasivePatterns

/-- **Lemma 5.3 (Primitive Wronskian isolates a root).** Let `Q ∈ ℤ[z]` have constant term `1`,
nonzero coefficients in `{±1}`, rigid support and full autocorrelation norm
`‖QQ^*‖₁ = |supp Q|²`. If `cont(W_Q) = 1`, then `Q` has a simple root `α` such that
`Q(β) = 0`, `β/α` a root of unity `⟹ β = α` (10).

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Lemma 5.3, display (10), printed p. 8 (PDF p. 9), lines 252–254.

**Formalization Note** Roots are complex: `Q` is cast to `ℂ[z]`. "Simple" is root multiplicity
exactly `1`. "`β/α` a root of unity" is `(β/α)ⁿ = 1` for some `n > 0`. The support is cast to `ℤ`
for `Rigid`; `Q^* = Q.reverse`; `cont` is `Polynomial.content`. -/
theorem lemma_5_3 (Q : Polynomial ℤ) (hQ0 : Q.coeff 0 = 1)
    (hQpm : ∀ i, Q.coeff i ≠ 0 → Q.coeff i = 1 ∨ Q.coeff i = -1)
    (hrigid : Rigid (Q.support.image (fun n : ℕ => (n : ℤ))))
    (hnorm : l1Norm (Q * Q.reverse) = (Q.support.card : ℤ) ^ 2)
    (hcont : (recipWronskian Q).content = 1) :
    ∃ α : ℂ, (Q.map (Int.castRingHom ℂ)).IsRoot α ∧
      (Q.map (Int.castRingHom ℂ)).rootMultiplicity α = 1 ∧
      ∀ β : ℂ, (Q.map (Int.castRingHom ℂ)).IsRoot β →
        (∃ n : ℕ, 0 < n ∧ (β / α) ^ n = 1) → β = α := by sorry

end EvasivePatterns
