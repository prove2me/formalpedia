-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_largeSummand_spec
-- name    : BipHamCount.Deterministic.largeSummand_spec
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:41:09.698666+00:00
-- url     : https://prove2.me/theorems/d8d84a8b-6456-475a-91fa-47ce97974bdb
-- title:
--   Proposition 4.1: correctness and bit cost of a large summand
-- statement:
--   For zero–one matrices $A,B$ of order $m$ and equal-sized row and column sets $S,T$, the large-summand evaluator, given integer values $a,b$, returns
--   $$(-1)^{|\bar S|+1} a b\det A[\bar S,\bar T]\det B[\bar T,\bar S].$$
--   If $|a|,|b|\leq 2^u$, the evaluator uses polynomial bit work in $m,u$, independently of the initial counter, and its answer has polynomial bit length. The explicit polynomial in the formal statement includes materializing both ordered minors and evaluating their integer determinants. Setting $a,b$ to the two permanent values stored by the dynamic program yields the summand of Proposition 4.1.
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 4.4, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Programs

namespace BipHamCount.Deterministic

/-- Correctness and bit complexity of one large-term accumulation step. -/
theorem largeSummand_spec {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (hA : ZeroOne A) (hB : ZeroOne B) (S T : Finset (Fin m)) (h : T.card = S.card)
    (a b : ℤ) (u : ℕ) (ha : a.natAbs ≤ 2^u) (hb : b.natAbs ≤ 2^u) (s : ℕ) :
    let t := 1+(m+1)*(2+m+4)
    let p := fun l : ℕ => 1+l*(2*t+m+4)
    let g := p (m+1)+t+1+m+5
    let β := 100*(g+2)^4+8*(m+3)+16
    let h := 16*(m+3)
    let w := (m+1)*(10*(h*(h*(h*β))))+β+β
    let v := 2*u+2*p m+1
    let ℓ := 8*(m+1)^3+m*(2+m*3+1)
    let z := (largeSummand A B S T a b).run s
    (z.1 = (-1 : ℤ)^(Sᶜ.card+1)*a*b*minor A Sᶜ Tᶜ*minor B Tᶜ Sᶜ ∧ z.1.natAbs ≤ 2^v) ∧
      z.2 ≤ s+(4*(m+1)+2*ℓ+2*w+(m+2)^2+4*(2*v+3)^2) := by sorry

end BipHamCount.Deterministic
