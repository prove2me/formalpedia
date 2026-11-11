-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_lemma_4_3
-- name    : CorrBoundsPoly.ExactDegree.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:59:54.636208+00:00
-- url     : https://prove2.me/theorems/5e59a662-9f07-47de-a1e2-c79d55bf0daf
-- title:
--   Lemma 4.3 — the recursive core $F_s$: homogeneous, $\deg F_s=s$, $M(s)\le9s^2$, $\nu(F_s)\le1/3$, attained
-- statement:
--   For every integer $s\ge1$, the explicit core $F_s$ of the recursion (4.6) ($F_1=x_1$; $F_s=\sigma_{s,3s^2}$ for dyadic $s\ge2$; $F_s=\bigoplus_{j=1}^3E_a(X^{(j)})F_t(Y^{(j)})$ otherwise) is homogeneous and satisfies
--   $$\deg F_s=s,\qquad M(s)\le9s^2,\qquad \nu(F_s)\le\frac13. \tag{4.5}$$
--   Moreover $F_s$ attains its certificate against degree-$(s-1)$ tests: some Boolean function $u$ of degree at most $s-1$ has $|\mathbb E(-1)^{F_s+u}|=\nu(F_s)$.
--
--   This lemma provides, for every degree $s$, a core whose degree-$(s-1)$ correlation is exactly its rank defect and at most $1/3$; it is the core of the main theorem.
--
--   Differences from the source:
--   - encoding: "there is an explicit homogeneous polynomial $F_s$" → the statement is about the paper's construction (4.6), defined as `F s` on `Fin (M s)` with the explicit layout of the `Cores` definition; reason: "explicit" refers to this construction
--   - encoding: $\deg F_s=s$ → `IsDegExactly (evalFn (F s)) s` (and `IsHomogeneous s` for the polynomial); reason: the paper's degree of a Boolean polynomial is the multilinear degree (p. 1)
--   - reading: "attains its certificate against degree-$(s-1)$ tests" → some $u$ with `HasDegLE u (s - 1)` and $|\mathbb E(-1)^{F_s+u}|=\nu(F_s)$; reason: the meaning of attainment in Lemma 4.2
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 31 (PDF 33), Lemma 4.3, Eqs. (4.5), (4.6); proof pp. 31–32 (PDF 33–34)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_Rho
import Definitions.Def_CorrBoundsPoly_ExactDegree_Cores

namespace CorrBoundsPoly.ExactDegree

/-- **Lemma 4.3** (The recursive exact-degree core; Xin Li, *More on Correlation Bounds for
Polynomials*, p. 31, PDF 33). For every integer `s ≥ 1` the explicit core `F_s` of Eq. (4.6) is
homogeneous with `deg F_s = s`, `M(s) ≤ 9s²` and `ν(F_s) ≤ 1/3` (Eq. (4.5)), and `F_s` attains its
certificate against degree-`(s − 1)` tests: some Boolean function `u` of degree at most `s − 1` has
`|E(−1)^{F_s + u}| = ν(F_s)`. -/
theorem lemma_4_3 (s : ℕ) (hs : 1 ≤ s) :
    (F s).IsHomogeneous s ∧ IsDegExactly (evalFn (F s)) s ∧ M s ≤ 9 * s ^ 2 ∧
      nu (F s) ≤ 1 / 3 ∧
      ∃ u : BoolFn (Fin (M s)), HasDegLE u (s - 1) ∧ bias (evalFn (F s) + u) = nu (F s) := by sorry

end CorrBoundsPoly.ExactDegree
