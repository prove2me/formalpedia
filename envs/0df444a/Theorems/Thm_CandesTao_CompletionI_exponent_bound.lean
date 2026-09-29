-- Prove2me | Theorems.Thm_CandesTao_CompletionI_exponent_bound
-- name    : CandesTao.CompletionI.exponent_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:41:42.09507+00:00
-- url     : https://prove2.me/theorems/53baeece-bb6e-4645-bf57-ab9bc3c4e42f
-- title:
--   Lemma 5.1 — Exponent bound $|J|+|K|-|Q|-|\Omega| \le -|Q'|+1$
-- statement:
--   Fix $j, k \ge 0$ and let $(s,t)$ be an admissible pair of sequences indexed by $[j]\times\{0,1\}\times\{0,\dots,k\}$, with value sets $J$, $K$, set of visited pairs $\Omega$, set $Q$ of non-rook moves and set $Q' \subset Q$ of recycled non-rook moves (all as in the definition of admissible pairs). Then
--   $$|J| + |K| - |Q| - |\Omega| \le -|Q'| + 1 .$$
--
--   In the moment computation of Section V, $n^{|J|+|K|}$ counts the injections placing a configuration in the grid, $|Q|$ counts the small coefficients of non-rook moves and $|\Omega|$ the powers of $1/p$; the lemma turns the resulting bound into $n^{-|Q'|+1}$ per configuration.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2068, Lemma 5.1

import Definitions.Def_CandesTao_CompletionI_AdmissiblePair

namespace CandesTao.CompletionI

/-- Candès–Tao, Lemma 5.1 (Exponent Bound): for every admissible pair `(s, t)` indexed by
`[j] × {0,1} × {0,…,k}`, `|J| + |K| - |Q| - |Ω| ≤ -|Q'| + 1`. -/
theorem exponent_bound (j k : ℕ) (s t : PathIndex j k → ℕ)
    (h : IsAdmissible j k s t) :
    ((rowValues s).card : ℤ) + (colValues t).card - (nonRookMoves s t).card -
        (visitedPairs s t).card ≤
      -((recycledNonRookMoves s t).card : ℤ) + 1 := by sorry

end CandesTao.CompletionI
