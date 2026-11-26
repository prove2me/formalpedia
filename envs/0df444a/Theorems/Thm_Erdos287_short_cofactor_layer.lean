-- Prove2me | Theorems.Thm_Erdos287_short_cofactor_layer
-- name    : Erdos287.short_cofactor_layer
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:19:22.320613+00:00
-- url     : https://prove2.me/theorems/2895cec5-39f8-4f36-9c71-7c0738146887
-- title:
--   Prime-power layer with at most three consecutive candidate cofactors
-- statement:
--   Suppose $D\subseteq[m,M]$ has positive denominators summing reciprocally to one, $q=p^e$ for prime $p$ and $e\ge1$, and any two candidate cofactors for multiples of $q$ in $[m,M]$ differ by at most two. Then the selected $q$-layer is empty or, for its smallest cofactor $c$, exactly $\{c,c+1\}$, $\{c,c+2\}$ or $\{c,c+1,c+2\}$ in cofactor coordinates. These possibilities require $p$ to divide $2c+1$, $2c+2$ or $3c^2+6c+2$, respectively.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.short_cofactor_layer (D : Finset ℕ) (m M p e : ℕ) (hm : 0 < m) (hp : p.Prime) (he : 1 ≤ e)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hwindow : ∀ a b : ℕ, m ≤ a * p ^ e → b * p ^ e ≤ M → b ≤ a + 2) :
    let q := p ^ e
    let H := D.filter (fun n => q ∣ n)
    H = ∅ ∨ ∃ c : ℕ, 0 < c ∧
      ((H = {c * q, (c + 1) * q} ∧ p ∣ 2 * c + 1) ∨
       (H = {c * q, (c + 2) * q} ∧ p ∣ 2 * c + 2) ∨
       (H = {c * q, (c + 1) * q, (c + 2) * q} ∧ p ∣ 3 * c ^ 2 + 6 * c + 2)) := by sorry
