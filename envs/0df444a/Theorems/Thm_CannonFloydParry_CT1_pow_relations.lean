-- Prove2me | Theorems.Thm_CannonFloydParry_CT1_pow_relations
-- name    : CannonFloydParry.CT1_pow_relations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T19:48:07.284418+00:00
-- url     : https://prove2.me/theorems/20a95622-eedd-4acc-bd36-327a4e24ec77
-- title:
--   Lemma 5.6 — moving powers of $C_n$ past the $X_r$
-- statement:
--   In $T_1$, let $n \ge 1$, $1 \le m \le n+1$ and $0 \le r, s \le n$. Then
--
--   i) $C_n^m X_r$ equals $X_{r-m}C_{n+1}^m$ if $r \ge m$, $C_{n+1}^{m+1}$ if $r = m-1$, and $X_{r+(n+2-m)}C_{n+1}^{m+1}$ if $r < m-1$;
--
--   ii) $X_s^{-1}C_n^m$ equals $C_{n+1}^{m+1}X_{(s+m)-(n+2)}^{-1}$ if $s \ge (n+2)-m$, $C_{n+1}^m$ if $s = (n+1)-m$, and $C_{n+1}^mX_{s+m}^{-1}$ if $s \le n-m$;
--
--   iii) $C_n^m = X_{(n+1)-m}C_{n+1}^m$; iv) $C_n^m = C_{n+1}^{m+1}X_{m-1}^{-1}$; v) $C_n^{n+2} = 1$.
--
--   **Formalization Note.** The case conditions are written without natural-number subtraction ($r + 1 = m$, $r + 1 < m$, $n + 2 \le s + m$, $s + m = n + 1$, $s + m \le n$); every subtraction left in an index is non-truncating under its case's hypotheses.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 5, p. 238, Lemma 5.6

import Mathlib
import Definitions.Def_CannonFloydParry_T

namespace CannonFloydParry

theorem CT1_pow_relations (n m r s : ℕ) (hn : 0 < n) (hm : 1 ≤ m) (hmn : m ≤ n + 1)
    (hr : r ≤ n) (hs : s ≤ n) :
    (m ≤ r → CT1 n ^ m * XT1 r = XT1 (r - m) * CT1 (n + 1) ^ m) ∧
      (r + 1 = m → CT1 n ^ m * XT1 r = CT1 (n + 1) ^ (m + 1)) ∧
      (r + 1 < m → CT1 n ^ m * XT1 r = XT1 (r + (n + 2 - m)) * CT1 (n + 1) ^ (m + 1)) ∧
      (n + 2 ≤ s + m →
        (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ (m + 1) * (XT1 (s + m - (n + 2)))⁻¹) ∧
      (s + m = n + 1 → (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ m) ∧
      (s + m ≤ n → (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ m * (XT1 (s + m))⁻¹) ∧
      CT1 n ^ m = XT1 (n + 1 - m) * CT1 (n + 1) ^ m ∧
      CT1 n ^ m = CT1 (n + 1) ^ (m + 1) * (XT1 (m - 1))⁻¹ ∧
      CT1 n ^ (n + 2) = 1 := by
  sorry

end CannonFloydParry
