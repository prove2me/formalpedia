-- Prove2me | Theorems.Thm_FamousTheorems_von_staudt_clausen
-- name    : FamousTheorems.von_staudt_clausen
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T07:10:21.408048+00:00
-- url     : https://prove2.me/theorems/e0102a45-80b7-4b5c-b121-88f4c5916c4c
-- title:
--   The von Staudt–Clausen theorem
-- statement:
--   **The von Staudt–Clausen theorem.**
--
--   For every natural number $k$,
--   $$B_{2k} + \sum_{\substack{p \text{ prime} \\ (p-1) \mid 2k}} \frac{1}{p} \;\in\; \mathbb{Z}.$$
--
--   The Bernoulli numbers are rationals with wildly growing numerators, but their denominators are
--   completely transparent: the denominator of $B_{2k}$ is exactly the product of the primes $p$
--   with $p-1$ dividing $2k$, each appearing to the first power. So $B_2 = 1/6$ with $6 = 2\cdot3$,
--   $B_4 = -1/30$ with $30 = 2\cdot3\cdot5$, and $B_{10} = 5/66$ with $66 = 2\cdot3\cdot11$.
--
--   The theorem pins down the $p$-adic valuation of $B_{2k}$ at every prime at once, which is why
--   it underlies the Kummer congruences and the construction of the $p$-adic zeta function. It
--   also explains the irregular primes appearing in Kummer's work on Fermat's Last Theorem: those
--   are detected by the *numerators*, which this theorem shows are the only mysterious part.
--
--   Proved independently by von Staudt and Clausen in 1840.
--
--   **Formalization note.** The sum runs over primes below $2k+2$ with $(p-1) \mid 2k$, which
--   captures every relevant prime since $p-1 \le 2k$ forces $p < 2k+2$; membership in
--   `Set.range Int.cast` is integrality inside $\mathbb{Q}$. The result is Mathlib's
--   `Bernoulli.vonStaudt_clausen`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

open Filter Set Topology DirectSum

theorem von_staudt_clausen (k : ℕ) :
    bernoulli (2 * k) + ∑ p ∈ Finset.range (2 * k + 2) with p.Prime ∧ (p - 1) ∣ 2 * k,
      (1 : ℚ) / p ∈ Set.range Int.cast := by sorry

end FamousTheorems
