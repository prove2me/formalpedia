-- Prove2me | Theorems.Thm_Erdos287_adjacent_cofactor_classes
-- name    : Erdos287.adjacent_cofactor_classes
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:42:59.546594+00:00
-- url     : https://prove2.me/theorems/aebe5187-3223-4eb5-a833-8c390c920362
-- title:
--   Chinese remainder residue classes for simultaneous adjacent omissions
-- statement:
--   Fix prime powers $p^e,r^g$ with distinct primes and two adjacent multiples of these powers. Shifting their cofactors by $r^g t,p^e t$ preserves adjacency. If the two layers in a unit-fraction representation must use translated patterns from finite families $F,G$, each pattern smaller than its prime, at least $(p-K_F)_+(r-K_G)_+$ classes of $t$ modulo $pr$ force both adjacent integers omitted. Here $K_F=\sum_{T\in F}\max(|T|-1,0)$, and $K_G$ is defined similarly.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.adjacent_cofactor_classes (p r e g a b i j : ℕ) (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (he : 1 ≤ e) (hg : 1 ≤ g) (ha : 0 < a) (hb : 0 < b)
    (hadj : (a + i) * p ^ e + 1 = (b + j) * r ^ g)
    (F G : Finset (Finset ℕ))
    (hF : ∀ T ∈ F, T.card < p) (hG : ∀ T ∈ G, T.card < r) :
    ∃ B : Finset (ZMod (p * r)),
      (p - ∑ T ∈ F, (T.card - 1)) * (r - ∑ U ∈ G, (U.card - 1)) ≤ B.card ∧
      ∀ t : ℕ, (t : ZMod (p * r)) ∈ B →
        ∀ D : Finset ℕ, (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
        (∃ T ∈ F, T.image (fun d => (a + r ^ g * t + d) * p ^ e) =
          D.filter (fun n => p ^ e ∣ n)) →
        (∃ U ∈ G, U.image (fun d => (b + p ^ e * t + d) * r ^ g) =
          D.filter (fun n => r ^ g ∣ n)) →
        let x := (a + r ^ g * t + i) * p ^ e
        x ∉ D ∧ x + 1 ∉ D := by sorry
