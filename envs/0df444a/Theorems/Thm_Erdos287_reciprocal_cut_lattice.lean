-- Prove2me | Theorems.Thm_Erdos287_reciprocal_cut_lattice
-- name    : Erdos287.reciprocal_cut_lattice
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:43:36.547017+00:00
-- url     : https://prove2.me/theorems/8fc2ff4c-afef-4630-9710-cf06c4601965
-- title:
--   Lattice certificates for cuts of reciprocal sums
-- statement:
--   Let the disjoint sets $A,B$ contain all possible denominators, with positive common multiples $a,b$ respectively. Suppose a selected set $D\subseteq A\cup B$ has reciprocal sum $r$. Put $g=\gcd(a,b)$ and $L=\operatorname{lcm}(a,b)$. The partial reciprocal sums of $D\cap A$ and $D\cap B$ are $x/a$ and $y/b$ for nonnegative integers $x,y$. They satisfy $Lr=(b/g)x+(a/g)y$, with $x\le\sum_{n\in A} a/n$ and $y\le\sum_{n\in B} b/n$. If $r=1$, the reduced denominator of either partial sum divides $g$. In particular, if the total reciprocal mass of $A$ is below $1/g$, then $D$ contains no member of $A$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Related denominator-excess argument in Howe, Huffman, Kohlmeyer and Kruer, The sharp deficit in primitive signed reciprocal relations, section 5.2, https://hexagonmath.org/pdf/2611.00753v1.

import Mathlib

theorem Erdos287.reciprocal_cut_lattice (D A B : Finset ℕ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : ∀ n ∈ A, n ∣ a) (hB : ∀ n ∈ B, n ∣ b)
    (hdisj : Disjoint A B) (hD : D ⊆ A ∪ B) (r : ℚ)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = r) :
    let s := ∑ n ∈ D ∩ A, (1 : ℚ) / n
    let t := ∑ n ∈ D ∩ B, (1 : ℚ) / n
    let g := Nat.gcd a b
    (∃ x y : ℕ, s = (x : ℚ) / a ∧ t = (y : ℚ) / b ∧
      x ≤ (∑ n ∈ A, a / n) ∧ y ≤ (∑ n ∈ B, b / n) ∧
      ((Nat.lcm a b : ℕ) : ℚ) * r = (((b / g) * x + (a / g) * y : ℕ) : ℚ)) ∧
    (r = 1 → s.den ∣ g ∧
      ((∑ n ∈ A, (1 : ℚ) / n) < (1 : ℚ) / g → D ⊆ B)) := by sorry
