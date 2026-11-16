-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_C_2
-- name    : ElimAgree.Supplement.theorem_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:44:30.438963+00:00
-- url     : https://prove2.me/theorems/5b32057c-7de7-46f7-8b23-cc382546493e
-- title:
--   Theorem C.2 — zero error needs expected communication $\log(1/\beta)$
-- statement:
--   Under the hypotheses of Lemma 5.2: let $k\ge1$, and for $i\in[k]$ let $h_i=(-1)^{f_i}$ be row balanced under a product measure $\mu_i=\mu_{X_i}\times\mu_{Y_i}$ with normalized sign operator $H_i$, and put
--
--   $$\beta=\prod_{i=1}^k\big(1+\|H_i\|^2\big)-1.$$
--
--   Then every zero-error protocol for $\mathrm{Elim}(f_1,\dots,f_k)$ in which Alice outputs has worst-case expected communication at least $\log(1/\beta)$; if each $h_i$ is also column balanced, the same holds when each leaf designates its output party. Consequently there is an absolute constant $C$ such that for $n\ge2$ and every $k\ge1$
--
--   $$\Big|R^{\mathrm{pub},A}_{0,\exp}\big(\mathrm{Elim}(\mathrm{IP}_n^k)\big)-\max\{n-\log k,0\}\Big|\le C.$$
--
--   **Formalization Note** The output at a leaf is any function of the outputting party's input. The two-sided statement is a lower bound for every zero-error Alice-output protocol and an upper bound by one.
--
--   Differences from the source:
--   - reading: "under the hypotheses of Lemma 5.2, every zero-error protocol" → both cases of Lemma 5.2: row balance with Alice output, and row and column balance with the output party designated at each leaf; reason: Lemma 5.2 states these two cases
--   - reading: k instances (k ≥ 1 implicit) → 1 ≤ k; reason: with k = 0, β = 0
--   - reading: = max{n − log k, 0} + O(1) → ∃ absolute C chosen before n, k; lower bound for every zero-error Alice-output protocol, upper bound by one; reason: R_{0,exp} is a minimum; O(1) is absolute
--   - encoding: worst-case expected communication ≥ b → ENNReal.ofReal b ≤ sup over inputs of the expected path length; reason: a bound b ≤ 0 is satisfied either way
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem C.2, p.37 (PDF p.39); Lemma 5.2, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_ElimAgree_IsLaw
import Definitions.Def_ElimAgree_Supplement_Models
import Definitions.Def_ElimAgree_Supplement_SignOp

namespace ElimAgree

namespace Supplement

/-- Theorem C.2, Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.37. Under the hypotheses of Lemma 5.2, every zero-error protocol has worst-case
expected communication at least `log(1/β)`. Consequently, for `n ≥ 2`,
`R^{pub,A}_{0,exp}(Elim(IP_n^k)) = max{n − log k, 0} + O(1)`.

The hypotheses of Lemma 5.2 (p.20): for `i ∈ [k]`, `h_i = (−1)^{f_i}` is row balanced under a product
measure `µ_i = µ_{X_i} × µ_{Y_i}`, with normalized sign operator `H_i`, and
`β = Π_{i=1}^k (1 + ∥H_i∥²) − 1`; the protocol has Alice output; if each `h_i` is also column
balanced, each leaf may designate its output party.

**Formalization Note.** Both cases of Lemma 5.2 are stated. Zero error is failure probability `0` on
every input; leaves carry the outputting party's output as a function of that party's input.
`O(1)` is an absolute constant `C` chosen before `n` and `k`; the second part is for every `k ≥ 1`. -/
theorem theorem_C_2 :
    (∀ (k : ℕ), 1 ≤ k → ∀ (X Y : Fin k → Type) [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
      (f : ∀ i, X i → Y i → Bool) (μX : ∀ i, X i → ℝ) (μY : ∀ i, Y i → ℝ),
      (∀ i, IsLaw (μX i)) → (∀ i, IsLaw (μY i)) → (∀ i, RowBalanced (μY i) (f i)) →
      (∀ μ : PMF (AliceProt (∀ i, X i) (∀ i, Y i) (Fin k → Bool)),
        (∀ x y, aliceErr (elimAns f) μ x y = 0) →
        ENNReal.ofReal (Real.logb 2
          (1 / (∏ i, (1 + signNorm (μX i) (μY i) (f i) ^ 2) - 1))) ≤ worstExpComm μ) ∧
      ((∀ i, ColBalanced (μX i) (f i)) →
        ∀ μ : PMF (DesProt (∀ i, X i) (∀ i, Y i) (Fin k → Bool)),
        (∀ x y, desErr (elimAns f) μ x y = 0) →
        ENNReal.ofReal (Real.logb 2
          (1 / (∏ i, (1 + signNorm (μX i) (μY i) (f i) ^ 2) - 1))) ≤ worstExpComm μ)) ∧
    (∃ C : ℝ, ∀ n k : ℕ, 2 ≤ n → 1 ≤ k →
      (∀ μ : PMF (AliceProt (Fin k → Fin n → Bool) (Fin k → Fin n → Bool) (Fin k → Bool)),
        (∀ x y, aliceErr (elimAns (X := fun _ => Fin n → Bool) (Y := fun _ => Fin n → Bool)
          (fun _ : Fin k => ipFun n)) μ x y = 0) →
        ENNReal.ofReal (max ((n : ℝ) - Real.logb 2 k) 0 - C) ≤ worstExpComm μ) ∧
      ∃ μ : PMF (AliceProt (Fin k → Fin n → Bool) (Fin k → Fin n → Bool) (Fin k → Bool)),
        (∀ x y, aliceErr (elimAns (X := fun _ => Fin n → Bool) (Y := fun _ => Fin n → Bool)
          (fun _ : Fin k => ipFun n)) μ x y = 0) ∧
        worstExpComm μ ≤ ENNReal.ofReal (max ((n : ℝ) - Real.logb 2 k) 0 + C)) := by sorry

end Supplement

end ElimAgree
