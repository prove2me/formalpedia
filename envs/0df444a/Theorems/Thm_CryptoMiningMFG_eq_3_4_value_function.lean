-- Prove2me | Theorems.Thm_CryptoMiningMFG_eq_3_4_value_function
-- name    : CryptoMiningMFG.eq_3_4_value_function
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:50.77952+00:00
-- url     : https://prove2.me/theorems/f5c4fbd0-4730-4c5f-b91a-da9bf16ec6f1
-- title:
--   Eq. (3.4): $v(t,x)=U(x)e^{-\gamma w(r;\gamma)\mathcal K(T-t)/(1+M)^2}$, attained by the constant rate $a^*$
-- statement:
--   Assume exponential utility and let the mean hash rate be the constant $\bar\alpha\equiv a^*=\frac{\mathcal K M}{c(1+M)^2}w(r;\gamma)$. For every $t\in[t_0,T]$ and $x\in\mathbb R$:
--
--   1. the value function is
--   $$
--   v(t,x;a^*)=U(x)\,\exp\!\Big(-\gamma\,w(r;\gamma)\,\frac{\mathcal K(T-t)}{(1+M)^2}\Big);
--   $$
--   2. the constant hash rate $a^*$ attains it: under the constant control $a^*$, $\mathbb E[e^{-\gamma X_T}]$ is finite and $-\frac1\gamma\,\mathbb E[e^{-\gamma X_T}]=v(t,x;a^*)$.
--
--   The value function is the supremum (2.4) over all controls, so the first clause is a verification statement for the intensity-controlled reward process, and the second says the constant rate is optimal.
--
--   Differences from the source:
--   - reading: "(2.6) yields (3.3)": the optimal hash rate at the equilibrium is the constant a* → the constant control a* attains the supremum (2.4): its −(1/γ)E[e^{−γX_T}] equals v(t, x; a*), and that expectation is finite; reason: "optimal hash rate" means a control attaining the supremum (2.4)
--   - reading: r is "the value of the mining reward" (p.9), sign not stated → 0 < r (field r_pos of Model); reason: a reward has positive value; with r ≤ 0 one has w ≤ 0 and no positive mean hash rate exists
--   - generalization: M + 1 is the total number of miners, M a positive integer "assumed large" (p.9) → M any positive real number; reason: nothing in §3.1 uses integrality; every integer M ≥ 1 is an instance
--   - generalization: the supremum in (2.4) is over Markovian controls α_t = α(t, X_t) (p.10) → the supremum is over all non-anticipating controls: measurable, locally integrable hash-rate rules φ_j(s; τ₁,…,τ_j) ≥ 0 of time and of the miner's own reward history; reason: this class contains every Markov control whose closed loop is well defined, and the optimum (the constant rate a*) is Markov, so at the equilibrium the two value functions coincide; for every admissible ᾱ both value functions have the product form U(x)h(t) (translation invariance), so Δv/∂ₓv = w(r;γ) and (2.6) is the same in either class, and so are the equilibria
--   - encoding: E[U(X_T)] with U(x) = −(1/γ)e^{−γx} → −(1/γ) times the lower Lebesgue integral of e^{−γX_T} in [0, ∞], with the integrand set to 0 on the null event of infinitely many rewards by T; the reward process is built from i.i.d. Exp(1) clocks; reason: Lean convention; the event of infinitely many rewards has probability 0 because the intensity is at most 𝒦, so no instance changes
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, eq. (3.4) p.14 and proof of Proposition 3.1, p.15 ("The value function then satisfies ∂ₜh − γK/(1 + M)² w(r; γ) h = 0, with terminal condition h(T) = 1. Thus we have (3.4).")

import Mathlib
import Definitions.Def_CryptoMiningMFG_Value

namespace CryptoMiningMFG

/-- **The value function (3.4) at the equilibrium, attained by the constant hash rate.**
Li, Reppen, Sircar, *A Mean Field Games Model for Cryptocurrency Mining*, arXiv:1912.01952v2,
eq. (3.4), p.14, and proof of Proposition 3.1, p.15: "The value function then satisfies
∂ₜh − γ𝒦/(1 + M)² w(r; γ) h = 0, with terminal condition h(T) = 1. Thus we have (3.4)."

Against the constant mean hash rate `ᾱ ≡ a* = 𝒦 M w / (c (1 + M)²)`, for every `t ∈ [t0, T]` and
`x ∈ ℝ`:
1. `v(t, x; a*) = U(x) e^{−γ w(r;γ) 𝒦 (T − t) / (1 + M)²}`;
2. the constant hash rate `a*` attains it: `E[e^{−γ X_T}]` under the constant control `a*` is
   finite and `−(1/γ) E[e^{−γ X_T}] = v(t, x; a*)`. -/
theorem eq_3_4_value_function (P : Model) :
    ∀ t ∈ Set.Icc P.t0 P.T, ∀ x : ℝ,
      value P t x (fun _ => P.aStar)
          = P.U x * Real.exp (-P.γ * P.w * P.K * (P.T - t) / (1 + P.M) ^ 2) ∧
      costExp P (fun _ => P.aStar) t x (constControl P.aStar) ≠ ⊤ ∧
      -(1 / P.γ) * (costExp P (fun _ => P.aStar) t x (constControl P.aStar)).toReal
          = value P t x (fun _ => P.aStar) := by sorry

end CryptoMiningMFG
