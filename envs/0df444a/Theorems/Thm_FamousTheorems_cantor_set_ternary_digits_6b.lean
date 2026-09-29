-- Prove2me | Theorems.Thm_FamousTheorems_cantor_set_ternary_digits_6b
-- name    : FamousTheorems.cantor_set_ternary_digits_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:08.516808+00:00
-- url     : https://prove2.me/theorems/edb7b4fb-e350-4435-8e12-e1050c392ba1
-- title:
--   The Cantor set consists of the reals with ternary digits 0 and 2
-- statement:
--   **The Cantor set consists of the reals with ternary digits $0$ and $2$.** The middle-thirds Cantor set $C=\bigcap_n C_n$, where $C_0=[0,1]$ and $C_{n+1}$ removes the open middle third of each interval of $C_n$, is
--   $$C=\Big\{\sum_{i\ge1}\frac{a_i}{3^i}\ :\ a_i\in\{0,2\}\text{ for all }i\Big\}.$$
--
--   This description is the standard way to work with the Cantor set. It gives a bijection between $C$ and the infinite binary sequences, so $C$ is uncountable. It also gives the Cantor function and shows that $C$ is homeomorphic to $\{0,1\}^{\mathbb N}$.
--
--   **Formalization note.** Mathlib's `cantorSet_eq_zero_two_ofDigits`. `cantorSet` is defined as the intersection of the iterated middle-third sets, and `Real.ofDigits a` is $\sum_{i\ge0}a_i/3^{i+1}$ for a digit sequence `a : ℕ → Fin 3`. The condition $a_i\ne1$ says that every digit is $0$ or $2$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `cantorSet_eq_zero_two_ofDigits`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cantor_set_ternary_digits_6b : cantorSet = {x : ℝ | ∃ a : ℕ → Fin 3, (∀ i, a i ≠ 1) ∧ Real.ofDigits a = x} := by sorry

end FamousTheorems
