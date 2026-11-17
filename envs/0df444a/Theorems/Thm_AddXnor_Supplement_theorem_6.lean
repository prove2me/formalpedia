-- Prove2me | Theorems.Thm_AddXnor_Supplement_theorem_6
-- name    : AddXnor.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:33:32.582605+00:00
-- url     : https://prove2.me/theorems/ab8bd585-8c07-4b52-8904-7c2c1c36cddf
-- title:
--   Theorem 6 — Transposition differential
-- statement:
--   Let two operator strings agree except that an adjacent $(+,\mathrm{XNOR})$ pair is replaced by $(\mathrm{XNOR},+)$. For uniform independent $m$-bit operands,
--   $$
--   \Pr[E_A(x)=E_A(x')]=2\left(\frac58\right)^{m-1}-2^{-(m-1)}.
--   $$
--   The formula holds for every common prefix and suffix and therefore does not depend on the transposed pair's position.
--
--   Differences from the source:
--   - encoding: positions $1\le p\le q-1$ → a natural index $p$ with $p+1<q$, corresponding to the paper's position $p+1$; reason: Lean operator indices are 0-based
--   - encoding: probability over uniform operands → exact finite uniform probability over `(Fin (q+1) → BitVec m)`; reason: finite-type encoding with identical uniform weights
-- source:
--   Wang, Lv, Shen, Zhang, manuscript (sha256 405d6dda…), Theorem 6, pp.19–20 (PDF pp.19–20)

import Mathlib
import Definitions.Def_AddXnor_Supplement_core

set_option autoImplicit false

namespace AddXnor.Supplement

/-- **Theorem 6 (Transposition differential)** (Wang, Lv, Shen, Zhang,
*Add/XNOR Chains*, manuscript, sha256 405d6dda..., Theorem 6, pp.19--20
(PDF pp.19--20)).

Lean uses the 0-based position `p`; it is the paper's position `p+1`.  The hypotheses say that
`x'` replaces exactly the adjacent `(+,XNOR)` pair by `(XNOR,+)` and agrees on the whole common
prefix and suffix.  Since the value below is independent of `p`, the position-independence clause
is part of the quantified identity. -/
theorem theorem_6 (q m p : ℕ) (hq : 2 ≤ q) (hm : 1 ≤ m) (hp : p + 1 < q)
    (x x' : Fin q → Bool)
    (hpair : x ⟨p, by omega⟩ = false ∧ x ⟨p + 1, hp⟩ = true)
    (hpair' : x' ⟨p, by omega⟩ = true ∧ x' ⟨p + 1, hp⟩ = false)
    (hcommon : ∀ i : Fin q, (i : ℕ) ≠ p → (i : ℕ) ≠ p + 1 → x' i = x i) :
    collisionProb (m := m) x x' =
      2 * (5 / 8 : ℝ) ^ (m - 1) - (2 : ℝ) ^ (-(m - 1 : ℤ)) := by sorry

end AddXnor.Supplement
