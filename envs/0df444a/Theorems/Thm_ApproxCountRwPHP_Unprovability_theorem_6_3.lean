-- Prove2me | Theorems.Thm_ApproxCountRwPHP_Unprovability_theorem_6_3
-- name    : ApproxCountRwPHP.Unprovability.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:58:50.69728+00:00
-- url     : https://prove2.me/theorems/8c1ed545-7749-4731-a29d-ab5833cbcdaf
-- title:
--   Theorem 6.3 — winning strategy from an infinite model
-- statement:
--   Let L be a finite function-and-constant signature of maximum arity a, taking a=0 for constants only or an empty signature. Let φ be quantifier-free with k variable positions. Suppose an infinite L-structure M satisfies ∀x̄ ¬φ(x̄). For all N,m,h∈ℕ and all ε∈(0,1], if
--
--   $$N\ge10^5(a+1)^2m^2h^2\varepsilon^{-4}(\ln(2m))^2,$$
--
--   then the adversary has a winning adaptive strategy in Gφ(N;m,h,ε).
--
--   The m=0 and h=0 cases are included. In the zero-round case, the logarithm factor is read with its total zero value at zero; the game still requires a non-witnessing final partial structure. All three win conditions and the order “there exists an adversary strategy, for every inspector strategy” are preserved.
--
--   Differences from the source:
--   - generalization: a finite function-and-constant language L with exactly k free variables → an enumerated finite signature with constants at arity zero and k available variable slots, possibly unused; reason: every source instance is retained; unused coordinates can be omitted at nonempty game sizes, and at size zero extra coordinates only preclude witnesses
--   - encoding: RDTs on finite trees and three game win conditions → PMFs with a structural support-height bound and adaptive history functions; reason: bounded height over finite queries and answers implies finite support; singleton PMFs and half-mixture equality are exact
--   - encoding: the zero-round game and its size inequality → Real.log 0 = 0 when m=0, with ε still strictly positive; reason: this retains all natural parameters; no positive-round hypothesis is added
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), Theorem 6.3, equation (6.1), printed p. 35, PDF p. 37; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=37

import Definitions.Def_ApproxCountRwPHP_Unprovability_Game

namespace ApproxCountRwPHP.Unprovability

/-- Theorem 6.3, printed 35 / PDF 37. Every N,m,h, including zero, and every
ε in (0,1] is retained. The denominator exponent is exactly four. -/
theorem theorem_6_3 (S : Signature) (k : ℕ) (φ : S.language.BoundedFormula Empty k)
    (hφ : φ.IsQF) (M : Type) [S.language.Structure M] [Infinite M]
    (hM : ∀ xs : Fin k → M, ¬ φ.Realize Empty.elim xs)
    (N m h : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1)
    (hN : (N : ℝ) ≥ 10^5 * (maximumArity S + 1 : ℕ)^2 * (m : ℝ)^2 * (h : ℝ)^2 *
      ε^(-4 : ℤ) * (Real.log (2 * (m : ℝ)))^2) :
    adversaryWins (N := N) (h := h) φ m ε := by sorry

end ApproxCountRwPHP.Unprovability
