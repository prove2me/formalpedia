-- Prove2me | Theorems.Thm_FamousTheorems_kummer_theorem_binomial
-- name    : FamousTheorems.kummer_theorem_binomial
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:30.65309+00:00
-- url     : https://prove2.me/theorems/5e8a6a25-64d5-4097-ad17-c0467c9d9baf
-- title:
--   Kummer's theorem on binomial coefficients
-- statement:
--   **Kummer's theorem.** Let $p$ be a prime and $k\le n$. The exponent of $p$ in $\binom nk$ equals the number of carries when $k$ and $n-k$ are added in base $p$:
--   $$v_p\binom nk=\#\{\,i\ge1:\ k\bmod p^i+(n-k)\bmod p^i\ge p^i\,\}.$$
--
--   In particular $p\mid\binom nk$ exactly when adding $k$ and $n-k$ in base $p$ produces a carry. Together with Lucas's theorem this gives the arithmetic of binomial coefficients modulo prime powers. It is used, for example, in studying the divisibility of central binomial coefficients.
--
--   **Formalization note.** Mathlib's `padicValNat_choose`. The carry positions are counted over `Finset.Ico 1 b` for any `b` with $\log_pn<b$, which covers all digit positions. The $i$-th test `p ^ i ≤ k % p ^ i + (n - k) % p ^ i` is exactly a carry out of the $i$-th lowest digit.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `padicValNat_choose`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem kummer_theorem_binomial {p n k b : ℕ} [Fact p.Prime] (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    padicValNat p (n.choose k) =
      ((Finset.Ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card := by sorry

end FamousTheorems
