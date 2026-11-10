-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_proposition_3_1
-- name    : AcycTesting.NearLinear.proposition_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:35:59.301722+00:00
-- url     : https://prove2.me/theorems/789c3006-c0d0-45be-9bcf-6bfd3e3539f7
-- title:
--   Proposition 3.1 — the cost of girth conditioning: Pr[G_γ] ≥ exp(−C 64^γ log N) = e^{−o(N)}
-- statement:
--   There is an absolute constant $C>0$ such that for every girth scale $\gamma=\gamma(N)$ satisfying (3.1) ($\gamma\ge2$, $64^\gamma\log N=o(N)$), with $\Pi$ a tuple of 32 independent uniform permutations of $[N]$ and $G_\gamma$ the event that $\Gamma(\Pi)$ has weak girth greater than $\gamma$:
--   $$\Pr[G_\gamma]\ \ge\ \exp(-C\,64^{\gamma}\log N)\quad\text{for all sufficiently large even }N,$$
--   and $\Pr[G_\gamma]=e^{-o(N)}$, i.e. for every $\delta>0$, $\Pr[G_\gamma]\ge e^{-\delta N}$ for all sufficiently large even $N$. Conditioning on high girth therefore costs only a subexponential factor.
--
--   Differences from the source:
--   - encoding: (3.1): an integer γ = γ(N) ≥ 2 with 64^γ log N = o(N) → GirthScale γ: γ : ℕ → ℕ, γ N ≥ 2 for all N, and 64^(γ N) · log N / N → 0; reason: the meaning of o(N) along N → ∞, natural log (§3.1)
--   - encoding: N even (standing assumption of §3.2), [N], colours [32] → Even N, Fin N, Fin 32 (0-based colours); reason: Lean convention; the same tuples
--   - encoding: Pr / E over independent uniform permutations π1, …, π32 → probU / expU: uniform on PermTuple N = Fin 32 → Equiv.Perm (Fin N); reason: the product of independent uniform laws is uniform on tuples
--   - reading: Pr[Gγ] ≥ exp(−C 64^γ log N) "under (3.1)", C an absolute constant (§3.1) → ∃ C > 0 chosen before γ; the bound for all N ≥ N₀(γ), N even; reason: C is absolute by the §3.1 convention; the proof needs C64^γ + γτ_γ < N, which (3.1) gives only for large N
--   - encoding: = e^{−o(N)} → ∀ δ > 0, ∃ N₀, ∀ N ≥ N₀ even, e^{−δN} ≤ Pr[Gγ]; reason: meaning of a lower bound e^{−o(N)} on a probability
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 15 (PDF 18), Proposition 3.1

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_Digraphs
import Definitions.Def_AcycTesting_NearLinear_PermCores

namespace AcycTesting.NearLinear

/-- Proposition 3.1 (the cost of girth conditioning): one absolute constant `C` such that,
under (3.1), `Pr[G_γ] ≥ exp(-C 64^γ log N)` for all large even `N`, and `Pr[G_γ] = e^{-o(N)}`. -/
theorem proposition_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℕ → ℕ, GirthScale γ →
      (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
        Real.exp (-(C * (64 : ℝ) ^ (γ N) * Real.log N)) ≤
          probU (fun πs : PermTuple N => CoreGirthGT (occMaps πs) (γ N))) ∧
      (∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
        Real.exp (-(δ * N)) ≤
          probU (fun πs : PermTuple N => CoreGirthGT (occMaps πs) (γ N))) := by sorry

end AcycTesting.NearLinear
