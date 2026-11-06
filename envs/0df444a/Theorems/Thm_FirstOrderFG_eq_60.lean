-- Prove2me | Theorems.Thm_FirstOrderFG_eq_60
-- name    : FirstOrderFG.eq_60
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:44:58.438029+00:00
-- url     : https://prove2.me/theorems/642eb89f-4f12-4142-870d-300fcdd1ef38
-- title:
--   Eq. (60) — $\ln W\le W-1\le-\eta\langle p,\hat\ell\rangle+\eta^2\sum_jp_j\hat\ell_j^2/(1+\eta\hat\ell_j)$
-- statement:
--   Let $p$ be a distribution on $K$ arms, $\hat\ell\in[0,\infty)^K$ a nonnegative vector and $\eta>0$, and let $W=\sum_{j=1}^Kp_je^{-\eta\hat\ell_j}$ be the EXP3 normalizer. Then
--   $$
--   \ln W\ \le\ W-1\ \le\ -\eta\langle p,\hat\ell\rangle+\eta^2\sum_{j=1}^K\frac{p_j\hat\ell_j^2}{1+\eta\hat\ell_j}.
--   $$
--
--   This is the one-step bound behind the refined EXP3 analysis (Proposition A.4) and Eq. (63) of the base learner.
--
--   Differences from the source:
--   - generalization: $p_t$ the EXP3 iterate and $\hat\ell_t$ its nonnegative estimates → any distribution $p$ on the arms and any nonnegative vector $\hat\ell$; reason: the EXP3 iterate is a distribution and the estimates are nonnegative, so it specializes
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, proof of Proposition A.4, Eq. (60), p.21

import Mathlib

namespace FirstOrderFG

/-- **Eq. (60): the EXP3 normalizer bound.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, proof of Proposition A.4, Eq. (60), p.21:
"Denote by `W_t ≜ ∑_{j=1}^K p_{t,j} e^{−η ℓ̂_{t,j}}` the normalizer in Eq. (1). … we first bound
`ln W_t` as follows: `ln W_t ≤ W_t − 1 ≤ −η⟨p_t, ℓ̂_t⟩ + η² ∑_{j=1}^K p_{t,j} ℓ̂_{t,j}²/(1 + η ℓ̂_{t,j})`",
for nonnegative estimates `ℓ̂_t` and `η > 0`.

**Formalization Note.** Stated for every distribution `p` on the `K` arms (not only the EXP3
iterate `p_t`) and every nonnegative vector `ℓ̂`. -/
theorem eq_60 {K : ℕ} (p lh : Fin K → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (hl : ∀ j, 0 ≤ lh j) (η : ℝ) (hη : 0 < η) :
    let W := ∑ j, p j * Real.exp (-(η * lh j))
    Real.log W ≤ W - 1 ∧
      W - 1 ≤ -(η * ∑ j, p j * lh j) + η ^ 2 * ∑ j, p j * lh j ^ 2 / (1 + η * lh j) := by sorry

end FirstOrderFG
