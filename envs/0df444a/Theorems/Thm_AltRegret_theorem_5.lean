-- Prove2me | Theorems.Thm_AltRegret_theorem_5
-- name    : AltRegret.theorem_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T00:10:04.768721+00:00
-- url     : https://prove2.me/theorems/16f79b06-5bb7-4f0c-8b73-de11aba43dbe
-- title:
--   Theorem 5 (Monotonicity of potential) — $\Phi_{t+1}\le\Phi_t\le\log d$ (corrected: $\eta\ge0$)
-- statement:
--   Consider the alternation-aware Hedge algorithm with parameters $\eta$ and $\beta$, where
--   $$
--   0\le\eta\le\tfrac18,\qquad \beta=\frac\eta4 .
--   $$
--   Let $t\ge1$ and let the losses satisfy $c_s\in[-1,1]^d$ for $1\le s\le t$ (with $c_0=\mathbf 0$). Then the potential $\Phi$ of (2) satisfies
--   $$
--   \Phi_{t+1}\le\Phi_t\le\log d .
--   $$
--   So the potential never increases and stays below its initial value $\Phi_1=\log d$. With $\Phi_{T+1}\ge\eta R_{T,i}$ this gives the bound $R_{T,i}\le\log d/\eta$ on the alternating regret against every pure action.
--
--   Differences from the source:
--   - reading: Algorithm 1 (η = 1/8, β = 1/32) with "Assume η ≤ 1/8 and β = η/4" → the algorithm parametrized by (η, β); reason: the theorem varies η, which Algorithm 1 fixes; the proof of Theorem 1 (p.8) says "The choices η = 1/8 and β = 1/32 in Algorithm 1 satisfy the conditions in Lemma 1 and Theorem 5"
--   - correction: η ≤ 1/8 → 0 ≤ η ≤ 1/8; reason: for η < 0, β < 0 and the maximum defining Φ_t is +∞, so Φ_t ≤ log d fails. d = 1, η = −1/8, β = −1/32 give Φ_1 = sup_θ (−β θ²) = +∞ > 0 = log 1
--   - encoding: c_t ∈ [−1,1]^d for every round → c_s ∈ [−1,1]^d for 1 ≤ s ≤ t; reason: Φ_{t+1} and Φ_t read only c_0, …, c_t, so the bound on later rounds is not used and the two hypotheses give the same instances of the conclusion
--   - encoding: max over θ; [d]; c_0 = 0 → supremum over θ ∈ ℝ; Fin d; lossAt; reason: Lean convention; for β ≥ 0 the supremum is the maximum (eq. (2))
--   - encoding: d ≥ 1 (Δ_d is nonempty) → any d ∈ ℕ; reason: at d = 0, outside the paper's model, every sum is empty and every quantity is 0 = log 0, so the clause holds there and no instance with d ≥ 1 changes
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, Theorem 5, p.7 (proof pp.7–8)

import Mathlib
import Definitions.Def_AltRegret_potential

namespace AltRegret

/-- **Theorem 5 (Monotonicity of potential).** Tao–Zheng, arXiv:2608.24731, Theorem 5, p.7:
"Assume `η ≤ 1/8` and `β = η/4`. For every round `t ≥ 1`, we have `Φ_{t+1} ≤ Φ_t ≤ log d`."

For the algorithm with parameters `0 ≤ η ≤ 1/8`, `β = η/4`, every round `t ≥ 1` and every loss
sequence with `c_s ∈ [−1,1]^d` for `1 ≤ s ≤ t`: `Φ_{t+1} ≤ Φ_t` and `Φ_t ≤ log d`.

**Formalization Note.** `Φ_t` is `potential η β c t`, a supremum over `θ ∈ ℝ` (genuine since
`β ≥ 0`). The bound on the losses is assumed on the rounds `Φ_{t+1}` reads (`c₁, …, c_t`;
`c₀ = 0` by `lossAt`). `0 ≤ η` corrects the printed `η ≤ 1/8`: for `η < 0`, `β < 0` and the
maximum defining `Φ_t` is `+∞`. At `η = 0` both sides equal `log d`. For `d = 0` both sides are
`0 = log 0`. -/
theorem theorem_5 (η β : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8) (hβ : β = η / 4) {d : ℕ}
    (c : ℕ → Fin d → ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hc : ∀ s, 1 ≤ s → s ≤ t → ∀ i, c s i ∈ Set.Icc (-1 : ℝ) 1) :
    potential η β c (t + 1) ≤ potential η β c t ∧ potential η β c t ≤ Real.log d := by sorry

end AltRegret
