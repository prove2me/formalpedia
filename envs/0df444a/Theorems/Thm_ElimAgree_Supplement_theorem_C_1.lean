-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_C_1
-- name    : ElimAgree.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:43:59.491209+00:00
-- url     : https://prove2.me/theorems/f8170107-7f67-4fba-a021-5a8d2af199ab
-- title:
--   Theorem C.1 — zero error with expected communication $\max\{0,\lceil n-\log k\rceil\}+2$
-- statement:
--   For $k\ge1$ and arbitrary $f_1,\dots,f_k$ with $n$-bit Bob inputs,
--
--   $$R^{\mathrm{pub},A}_{0,\exp}\big(\mathrm{Elim}(f_1,\dots,f_k)\big)\ \le\ \max\{0,\lceil n-\log k\rceil\}+2,$$
--
--   where $R^{\mathrm{pub},A}_{0,\exp}$ is the least worst-case expected communication of a zero-error public-coin protocol with output at Alice.
--
--   So with expected communication the $\log k$ saving of Theorem 4.2 is kept even at zero error.
--
--   **Formalization Note** The claim is the existence of a distribution over protocol trees with Alice's output at the leaves, failure probability $0$ on every input, and worst-case expected path length at most the bound.
--
--   Differences from the source:
--   - reading: k instances (k ≥ 1 implicit) → 1 ≤ k; reason: log k is used
--   - encoding: R_{0,exp} ≤ b → some zero-error Alice-output protocol has worst-case expected communication ≤ b; reason: R_{0,exp} is a minimum over such protocols
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem C.1, p.37 (PDF p.39); R_{0,exp}, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_ElimAgree_Supplement_Models

namespace ElimAgree

namespace Supplement

/-- Theorem C.1, Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.37. For arbitrary `f_1, …, f_k` with `n`-bit Bob inputs,
`R^{pub,A}_{0,exp}(Elim(f_1, …, f_k)) ≤ max{0, ⌈n − log k⌉} + 2`.

**Formalization Note.** `R^{pub,A}_{0,exp}` is the minimum, over zero-error public-coin protocols
with output at Alice, of the worst-case expected communication (Appendix C, p.36); the claim is the
existence of a `PMF` over trees with Alice's output at the leaves, failure probability `0` on every
input, and `worstExpComm` at most the bound. Bob's inputs are `Fin n → Bool`; Alice's input types
and the `f_i` are arbitrary; `k ≥ 1`. -/
theorem theorem_C_1 (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (X : Fin k → Type)
    (f : ∀ i, X i → (Fin n → Bool) → Bool) :
    ∃ μ : PMF (AliceProt (∀ i, X i) (Fin k → Fin n → Bool) (Fin k → Bool)),
      (∀ x y, aliceErr (elimAns (Y := fun _ => Fin n → Bool) f) μ x y = 0) ∧
      worstExpComm μ ≤
        ENNReal.ofReal (max 0 ((⌈(n : ℝ) - Real.logb 2 k⌉ : ℤ) : ℝ) + 2) := by sorry

end Supplement

end ElimAgree
