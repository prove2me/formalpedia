-- Prove2me | Theorems.Thm_DelayedGamesMAO_lemma_5
-- name    : DelayedGamesMAO.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:56.382245+00:00
-- url     : https://prove2.me/theorems/13831431-b9cb-4aff-9c70-73bc8c3f1d5d
-- title:
--   Lemma 5 — the coefficients (8) are nonnegative and conserve flow
-- statement:
--   Let $T\ge1$, $(d_t)$ delays with $t+d_t\le T$, $\gamma>0$, $0=\eta_1\le\dots\le\eta_{T+1}$, and $\alpha$ an allocation schedule. Then the coefficients $c^{(t+1)}_s$ of (8) satisfy
--
--   1. $c^{(t+1)}_s\ge0$ for every $0\le s\le t\le T$;
--   2. $A^{\mathrm{in}}_t=A^{\mathrm{out}}_t$ for every $t\in[T]$.
--
--   Flow conservation makes the multi-anchor potential of Theorem 6 vanish, so only the weight injected at $w_0$ is paid for.
--
--   Differences from the source:
--   - reading: allocation schedule (α^{(t)}_k)_{1≤s≤t≤T} → an allocation schedule in the sense of Definition 1, an array up to T + 1; reason: the proof uses α^{(T+1)}_t = 0 by property (S2) of Definition 1, which defines schedules up to T + 1
--   - encoding: β_t = η_t + γQ_t with β_0 = 0; Q_t for t ∈ [T] → β_0 = 0 set explicitly; Q_t = max_{s∈[t]} q_s for every t, so Q_{T+1} = Q_T; reason: (8) reads β_{T+1}; the formula's value is the one the proofs use
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
--   - encoding: rounds 1, …, T (and T + 1) and finite sequences indexed by them → natural numbers and sequences ℕ → … whose terms outside the used indices are unconstrained; reason: only the paper's indices are read; same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §6.3, Lemma 5, p.19

import Mathlib
import Definitions.Def_DelayedGamesMAO_IsAllocationSchedule
import Definitions.Def_DelayedGamesMAO_coef
import Definitions.Def_DelayedGamesMAO_Ain
import Definitions.Def_DelayedGamesMAO_Aout

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Lemma 5 (the coefficients (8) are nonnegative and conserve flow).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §6.3, Lemma 5, p.19: "Given any `γ > 0`, any sequence `0 = η_1 ≤ ⋯ ≤ η_{T+1}`, and any
allocation schedule `(α_k^{(t)})_{1≤s≤t≤T}`, the corresponding coefficients `(c_s^{(t+1)})_{0≤s≤t≤T}`
from Equation (8) satisfy: (i) `c_s^{(t+1)} ≥ 0` for every `0 ≤ s ≤ t ≤ T`; (ii) `A_t^{in} = A_t^{out}`
for every `t ∈ [T]`."

**Formalization Note.** The schedule's index range is printed `1 ≤ s ≤ t ≤ T`; the proof uses
`α_t^{(T+1)} = 0` "by property (S2) of Definition 1", i.e. the Definition-1 array up to `T + 1`,
which is `IsAllocationSchedule`. The coefficients are `coef d γ η α` (`coef d γ η α t s = c_s^{(t)}`).
The proof "recall[s] that we assume `t + d_t ≤ T`", a hypothesis here. -/
theorem lemma_5 (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T)
    (γ : ℝ) (hγ : 0 < γ) (η : ℕ → ℝ) (hη1 : η 1 = 0)
    (hηmono : ∀ t ∈ Finset.Icc 1 T, η t ≤ η (t + 1))
    (α : ℕ → ℕ → ℝ) (hα : IsAllocationSchedule d T α) :
    (∀ t ∈ Finset.range (T + 1), ∀ s ∈ Finset.range (t + 1), 0 ≤ coef d γ η α (t + 1) s) ∧
      ∀ t ∈ Finset.Icc 1 T, Ain (coef d γ η α) t = Aout (coef d γ η α) T t := by sorry

end DelayedGamesMAO
