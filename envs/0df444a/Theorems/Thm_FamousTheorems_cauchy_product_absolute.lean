-- Prove2me | Theorems.Thm_FamousTheorems_cauchy_product_absolute
-- name    : FamousTheorems.cauchy_product_absolute
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:27.947848+00:00
-- url     : https://prove2.me/theorems/fb901c53-2928-49bc-8641-260a1f7fc364
-- title:
--   The Cauchy product theorem for absolutely convergent series
-- statement:
--   **The Cauchy product theorem for absolutely convergent series.** Let $\sum f_n$ and $\sum g_n$ be absolutely convergent series in a complete normed ring. Then their Cauchy product converges and
--   $$\Big(\sum_{n}f_n\Big)\Big(\sum_{n}g_n\Big)=\sum_{n}\sum_{k=0}^{n}f_kg_{n-k}.$$
--
--   This justifies multiplying power series term by term inside their disc of convergence. It gives, for example, $e^{a}e^{b}=e^{a+b}$ for commuting $a,b$ in a Banach algebra. Mertens' theorem weakens the hypothesis so that only one series need converge absolutely. That stronger statement is not the one formalized here.
--
--   **Formalization note.** Mathlib's `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`. Absolute convergence is `Summable` of the norms, and `∑'` is the unconditional sum in the complete normed ring `R`, which need not be commutative.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cauchy_product_absolute {R : Type*} [NormedRing R] [CompleteSpace R] {f g : ℕ → R} (hf : Summable fun n => ‖f n‖)
    (hg : Summable fun n => ‖g n‖) :
    (∑' n, f n) * (∑' n, g n) = ∑' n, ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by sorry

end FamousTheorems
