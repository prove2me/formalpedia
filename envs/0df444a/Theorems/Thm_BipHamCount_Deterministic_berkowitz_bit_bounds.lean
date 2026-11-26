-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_berkowitz_bit_bounds
-- name    : BipHamCount.Deterministic.berkowitz_bit_bounds
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:31:39.936591+00:00
-- url     : https://prove2.me/theorems/e92d4ceb-0aad-5615-8179-9875b28a92a6
-- title:
--   Polynomial bit complexity and coefficient bounds for the implemented Berkowitz determinants
-- statement:
--   Consider the division-free integer and polynomial determinant programs used in Section 4, on an input of matrix order $n$. Suppose $u\geq 1$, all absolute integer coefficients are at most $2^u$, and every input polynomial coefficient array has length at most $u$. Define
--   $$t=u+(n+1)(2u+n+4),\qquad p(l)=1+l(2t+n+4),\qquad g=p(n+1)+t+u+n+5.$$
--   With $b=100(g+2)^4+8(n+3)+16$ and $h=16(n+3)$, the increase in the actual bit-work counter is at most
--   $$10(n+1)h^3 b+2b.$$
--   For integer inputs the magnitude of the result is at most $2^{p(n)}$. For polynomial inputs the returned coefficient array has length at most $p(n)$ and each coefficient has magnitude at most $2^{p(n)}$. This applies to every initial counter and includes all intermediate arithmetic and loop overhead in the fixed programs.
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 4.4, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Arithmetic

namespace BipHamCount.Deterministic

/-- Bit complexity and output-size bounds for the two Berkowitz programs. -/
theorem berkowitz_bit_bounds (n u : ℕ) (hu : 1 ≤ u) :
    let t := u + (n+1)*(2*u+n+4)
    let p := fun l : ℕ => 1+l*(2*t+n+4)
    let g := p (n+1)+t+u+n+5
    let b := 100*(g+2)^4+8*(n+3)+16
    let h := 16*(n+3)
    let w := (n+1)*(10*(h*(h*(h*b))))+b+b
    (∀ (M : Array (Array ℤ)) (s : ℕ),
      (∀ i j : ℕ, (((M[i]?.getD #[])[j]?).getD 0).natAbs ≤ 2^u) →
      let z := (berkowitz intOps n M).run s
      z.1.natAbs ≤ 2^(p n) ∧ z.2 ≤ s+w) ∧
    (∀ (M : Array (Array ZPoly)) (s : ℕ),
      (∀ i j : ℕ, let a := ((M[i]?.getD #[])[j]?).getD #[]
        a.size ≤ u ∧ ∀ k : ℕ, (a[k]?.getD 0).natAbs ≤ 2^u) →
      let z := (berkowitz polyOps n M).run s
      (z.1.size ≤ p n ∧ ∀ k : ℕ, (z.1[k]?.getD 0).natAbs ≤ 2^(p n)) ∧ z.2 ≤ s+w) := by sorry

end BipHamCount.Deterministic
