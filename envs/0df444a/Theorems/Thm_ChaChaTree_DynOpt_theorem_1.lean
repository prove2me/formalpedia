-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_theorem_1
-- name    : ChaChaTree.DynOpt.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:21:59.194943+00:00
-- url     : https://prove2.me/theorems/cf56739f-c60c-4b5b-b28e-4680272f4ec8
-- title:
--   Theorem 1 (Main) — an online BST serves every access sequence in (OPT(X) + n)·O(log log log n)
-- statement:
--   There are a constant $C$ and, for every $n$, a deterministic online binary search tree algorithm $A_n$ on the keys $[n]$, in the BST model of §5.1, such that for every $n \ge 1$ and every access sequence $X$ on $[n]$, $A_n$ serves $X$ and its total cost satisfies
--   $$\mathrm{cost}(A_n, X) \le C\,\big(\mathrm{OPT}(X) + n\big)\,\max\big(1, \log\log\log n\big),$$
--   where $\mathrm{OPT}(X)$ is the minimum cost of any offline execution of $X$ in the same model (free initial tree). "Online" means that the actions of access $t$ depend only on $x_1,\dots,x_t$ (and $n$), and the initial tree does not depend on $X$.
--
--   The paper proves this by the chain on p. 9 and pp. 34–35: cost $\le O((n + M + \mathrm{Flips}_2)\lambda)$ (Theorem 36 with Theorem 34) $\le O((n + m + \mathrm{Alt} + \mathrm{DepthAlt})\lambda)$ (Theorem 34's displays and Lemma 27) $\le O((n + m + \mathrm{IR})\lambda)$ (Lemma 18 and §2.2) $\le O((n + \mathrm{OPT})\lambda)$ (Lemma 4), with $\lambda = O(\log\log\log n)$ for a balanced $T_2$, extended to all $n$ by App. B.3 (pp. 80–81).
--
--   Differences from the source:
--   - reading: the self-adjusting Cha-cha trees are online binary search trees that serve every X in (OPT(X) + n)·O(log log log n) time → ∃ C, ∃ (A n : OnlineBSTAlg n) for every n, serving every X on [n] with cost ≤ C·(OPT n X + n)·max 1 (log log log n); reason: 'Cha-cha trees' names the paper's witness, whose standard-BST realization (App. A) is assembled from cited simulations ([MPWZ19], [DILÖ13, Theorem 7]) and is not specified to the level of a Lean definition; the theorem's 'i.e.' clause is the existence of an online deterministic BST with this guarantee
--   - encoding: O(log log log n) → C · max 1 (logb 2 (logb 2 (logb 2 n))) with C quantified before n and X; reason: the iterated logarithm is nonpositive or undefined at some small n, and is below 1 for 4 < n < 16 in base 2; the asymptotic factor has a positive floor for small n, absorbed into the uniform constant (cf. INSIGHTS I1)
--   - encoding: time → the number of unit-cost actions of the §5.1 BST model; reason: §5.1 defines the cost of an algorithm on X as its total number of actions
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Theorem 1, p. 2 (PDF 3); proof p. 9 (PDF 10), pp. 34–35 (PDF 35–36), App. B.3 'Extension to arbitrary numbers of keys', pp. 80–81 (PDF 81–82)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_CursorModel

set_option autoImplicit false

namespace ChaChaTree.DynOpt

open Real

/-- **Theorem 1 (Main)** (p. 2). There are a constant `C` and, for every `n`, a deterministic
online binary search tree algorithm on the keys `[n]` (BST model of §5.1) that serves every access
sequence `X` on `[n]` at total cost at most `C·(OPT(X) + n)·max(1, log log log n)`, where `OPT(X)`
is the minimum cost of any offline execution of `X` in the same model. -/
theorem theorem_1 :
    ∃ C : ℝ, ∃ A : ∀ n : ℕ, OnlineBSTAlg n, ∀ n : ℕ, 1 ≤ n →
      ∀ X : List ℕ, (∀ x ∈ X, x ∈ Finset.Icc 1 n) →
        (A n).Serves X ∧
          ((A n).cost X : ℝ) ≤
            C * ((OPT n X : ℝ) + n) * max 1 (logb 2 (logb 2 (logb 2 n))) := by sorry

end ChaChaTree.DynOpt
