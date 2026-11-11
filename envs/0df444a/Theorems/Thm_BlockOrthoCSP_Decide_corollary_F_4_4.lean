-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_corollary_F_4_4
-- name    : BlockOrthoCSP.Decide.corollary_F_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:15:13.287516+00:00
-- url     : https://prove2.me/theorems/fcca187a-e33a-4a0f-8406-52860e8d6986
-- title:
--   Corollary F.4.4 — $B_k$ is cut out by the finite set $Q_k$ of product polynomials, and $Q_k$ is computable from $D$, $k$ and $\mu(K)$
-- statement:
--   Let $q \ge 1$, $\mathcal F$ a finite set of algebraic-valued constraint functions on $D$, $K$ its field (F.13), $k \ge 2$. For every $K$-valued $A$ on $D^k$,
--   $$A \in B_k \iff P(A) = 0 \text{ for every } P \in Q_k. \qquad (F.26)$$
--   Moreover $Q_k$ is effectively computable from $D$, $k$ and $\mu(K)$: one computable map sends $(q, k, \text{exact codes of the elements of } \mu(K))$ to a list of polynomial codes whose decoded set is exactly $Q_k$.
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: a function of arity r ≥ 2 (or k ≥ 2), rows F(x, ∗) indexed by x ∈ D^{r−1} → arity j + 1 with 1 ≤ j; rows indexed by Fin j → Fin q, the column is the last coordinate (Fin.snoc); reason: the same functions; writing r = j + 1 avoids natural-number subtraction
--   - encoding: there is a (total, exact) algorithm → ∃ a function on codes with Mathlib's Computable, correct on every valid input; reason: Mathlib computability (partial recursive functions over Primcodable codes) is the meaning of 'algorithm'; a total computable function halts on every input
--   - encoding: Q_k 'effectively computable from D, k, and µ(K)' → one Computable f : (q, k, list of AlgCodes of µ(K)) → list of polynomial codes (coefficients AlgCodes, variables X_a coded by the entries of a), uniform in q, k and F, whose decoded set equals Qk F j whenever the input codes are valid and list exactly µ(K); reason: µ(K) is input by exact codes of its elements; uniformity is what 'computable from D, k, µ(K)' means
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-18, Corollary F.4.4

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Certificate
import Definitions.Def_BlockOrthoCSP_Decide_Codes

namespace BlockOrthoCSP.Decide

/-- Corollary F.4.4 (polynomial identities for the BO locus), p. F-18, for arity `k = j + 1`:
(F.26), and `Q_k` is computable from `D` (i.e. `q`), `k` and `µ(K)` (given by exact codes of its
elements), uniformly. -/
theorem corollary_F_4_4 :
    (∀ (q : ℕ), 1 ≤ q → ∀ F : Finset (CFn q), IsAlgLanguage F → ∀ j : ℕ, 1 ≤ j →
      ∀ A : (Fin (j + 1) → Fin q) → ℂ, (∀ a, A a ∈ fieldK F) →
        (A ∈ Bk F j ↔ ∀ P ∈ Qk F j, MvPolynomial.eval A P = 0)) ∧
    ∃ f : ℕ × ℕ × List AlgCode → List (PolyCode (List ℕ)), Computable f ∧
      ∀ (q : ℕ), 1 ≤ q → ∀ F : Finset (CFn q), IsAlgLanguage F → ∀ j : ℕ, 1 ≤ j →
        ∀ cs : List AlgCode, (∀ c ∈ cs, c.Valid) → {z | ∃ c ∈ cs, c.val = z} = muK F →
          {P | ∃ pc ∈ f (q, j + 1, cs), pc.decode (decodeTuple q (j + 1)) = P} = Qk F j := by sorry

end BlockOrthoCSP.Decide
