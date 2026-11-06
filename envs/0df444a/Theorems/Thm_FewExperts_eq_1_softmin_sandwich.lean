-- Prove2me | Theorems.Thm_FewExperts_eq_1_softmin_sandwich
-- name    : FewExperts.eq_1_softmin_sandwich
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:53:06.916491+00:00
-- url     : https://prove2.me/theorems/fffcdd46-d90a-4c55-9ee7-b7f894d1421f
-- title:
--   Eq. (1) — $\min_i a^i-\frac{\ln N}{\eta}\le S\le\min_i a^i$
-- statement:
--   For $N\ge1$ reals $a^1,\dots,a^N$ and a learning rate $\eta>0$, the softmin $S=-\frac1\eta\ln\sum_i e^{-\eta a^i}$ satisfies
--
--   $$
--   \min_i a^i-\frac{\ln N}{\eta}\le S\le\min_i a^i .
--   $$
--
--   The proof of Theorem 4 uses both sides. The upper bound turns a large potential into a large minimum shifted advantage. The lower bound restores the potential after the scale $L$ doubles.
--
--   Differences from the source:
--   - encoding: a learning rate η (η = Θ̃(1/L)) → an explicit hypothesis η > 0; reason: the paper's learning rates 8s/L are positive
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §2.4, eq. (1), p.8 (PDF p.9)

import Mathlib
import Definitions.Def_FewExperts_softmin

namespace FewExperts

/-- **Equation (1): the softmin sandwich.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §2.4, (1), p.8 (PDF 9): "S_t = −(1/η) ln ∑_i e^{−η a_t^i}, which is the softmin of
the shifted advantages with learning rate η … It satisfies
min_i a_t^i − (ln N)/η ≤ S_t ≤ min_i a_t^i."

For `N ≥ 1` reals `a i` and `η > 0`,
`min_i a_i − (ln N)/η ≤ softmin η a ≤ min_i a_i`.

**Formalization Note** `min_i` is `⨅ i` over the nonempty finite type `Fin N`; `ln` is
`Real.log`. -/
theorem eq_1_softmin_sandwich (N : ℕ) [NeZero N] (η : ℝ) (hη : 0 < η) (a : Fin N → ℝ) :
    (⨅ i, a i) - Real.log N / η ≤ softmin η a ∧ softmin η a ≤ ⨅ i, a i := by sorry

end FewExperts
