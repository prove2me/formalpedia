-- Prove2me | Theorems.Thm_Erdos287_adjacent_full_cofactor_classes
-- name    : Erdos287.adjacent_full_cofactor_classes
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:57:15.226749+00:00
-- url     : https://prove2.me/theorems/502a1280-1ae4-44dd-a46d-ef61988607cd
-- title:
--   Adjacent omissions across the full carry periods of two prime-power layers
-- statement:
--   Fix powers $p^e,r^g$ of distinct primes and neighboring multiples, with translated pattern families of diameter less than $p^{h+1}$ and $r^{k+1}$. Let $R_p,R_r$ be the full carry tables at periods $P=p^{2h+1}$ and $Q=r^{2k+1}$. Among the Chinese remainder parameter classes modulo $PQ$, precisely $(P-|R_p|)(Q-|R_r|)$ fail both cofactor tests. In these classes both neighboring positions are absent from any unit-fraction representation satisfying the template hypotheses.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.adjacent_full_cofactor_classes (p r e g a b i j h k : ℕ) (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (he : 1 ≤ e) (hg : 1 ≤ g) (ha : 0 < a) (hb : 0 < b)
    (hadj : (a + i) * p ^ e + 1 = (b + j) * r ^ g)
    (F G : Finset (Finset ℕ))
    (hF : ∀ T ∈ F, ∀ x ∈ T, ∀ y ∈ T, x < y + p ^ (h + 1))
    (hG : ∀ T ∈ G, ∀ x ∈ T, ∀ y ∈ T, x < y + r ^ (k + 1)) :
    let P := p ^ (2 * h + 1)
    let Q := r ^ (2 * k + 1)
    ∃ (Rp : Finset (ZMod P)) (Rr : Finset (ZMod Q)) (B : Finset (ZMod (P * Q))),
      (∀ z : ZMod P, z ∈ Rp ↔ ∃ T ∈ F, T.Nonempty ∧
        let c := z.val + P
        let L := ∏ d ∈ T, (c + d)
        p ^ (padicValNat p L + 1) ∣ ∑ u ∈ T, ∏ d ∈ T.erase u, (c + d)) ∧
      (∀ z : ZMod Q, z ∈ Rr ↔ ∃ T ∈ G, T.Nonempty ∧
        let c := z.val + Q
        let L := ∏ d ∈ T, (c + d)
        r ^ (padicValNat r L + 1) ∣ ∑ u ∈ T, ∏ d ∈ T.erase u, (c + d)) ∧
      B.card = (P - Rp.card) * (Q - Rr.card) ∧
      (∀ t : ℕ, (t : ZMod (P * Q)) ∈ B ↔
        ((a + r ^ g * t : ℕ) : ZMod P) ∉ Rp ∧ ((b + p ^ e * t : ℕ) : ZMod Q) ∉ Rr) ∧
      ∀ t : ℕ, (t : ZMod (P * Q)) ∈ B →
        ∀ D : Finset ℕ, (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
        (∃ T ∈ F, T.image (fun d => (a + r ^ g * t + d) * p ^ e) =
          D.filter (fun n => p ^ e ∣ n)) →
        (∃ U ∈ G, U.image (fun d => (b + p ^ e * t + d) * r ^ g) =
          D.filter (fun n => r ^ g ∣ n)) →
        let x := (a + r ^ g * t + i) * p ^ e
        x ∉ D ∧ x + 1 ∉ D := by sorry
