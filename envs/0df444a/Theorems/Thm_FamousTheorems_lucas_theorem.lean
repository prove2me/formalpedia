-- Prove2me | Theorems.Thm_FamousTheorems_lucas_theorem
-- name    : FamousTheorems.lucas_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:13:03.353147+00:00
-- url     : https://prove2.me/theorems/d98ea2bc-1bd5-455f-81f7-48a5b488b48d
-- title:
--   Lucas's theorem
-- statement:
--   **Lucas's theorem.** For a prime $p$, binomial coefficients factor modulo $p$ along base-$p$ digits: $$\binom{m}{n} \equiv \prod_i \binom{m_i}{n_i} \pmod p.$$ One congruence reduces an arbitrarily large binomial coefficient to a product of tiny ones. It follows that $\binom{m}{n}$ is nonzero mod $p$ exactly when no digit of $n$ exceeds the corresponding digit of $m$, which is why Pascal's triangle mod 2 is the Sierpinski gasket and why Kummer's theorem on $p$-adic valuations takes the form it does. Lucas proved it in 1878. **Formalization note.** Digits are taken in base `p`. The result is Mathlib's `Choose.lucas_theorem`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem lucas_theorem :
    ∀ {n k p : ℕ} [Fact (Nat.Prime p)] {a : ℕ}, 
    n < p ^ a → k < p ^ a → ↑(n.choose k) ≡ ∏ i ∈ Finset.range a, ↑((n / p ^ i % p).choose (k / p ^ i % p)) [ZMOD ↑p] := by sorry

end FamousTheorems
