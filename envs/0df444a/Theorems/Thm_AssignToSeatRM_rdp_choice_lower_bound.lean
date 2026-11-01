-- Prove2me | Theorems.Thm_AssignToSeatRM_rdp_choice_lower_bound
-- name    : AssignToSeatRM.rdp_choice_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:52.216628+00:00
-- url     : https://prove2.me/theorems/c50d9f10-394a-4a9e-a370-388e44f020ab
-- title:
--   Proof of Theorem 4, p.ec23 (corrected: denominator $i(M+1-j)+1$) — RDP's chosen coordinate is at least $d_{ij}/(i(M+1-j)+1)$
-- statement:
--   Let $A\in\mathbb N^{\{u\le v\}}$ be maximal-sequence counts, $d\ge0$ demands, $i\to j$ an itinerary ($1\le i\le j\le M$), and $\gamma$ a feasible solution of the dynamic primal (14). Let $o$ be an option of Algorithm 3, line 4, of maximal value: either the rejection $[0,0]$, with value $\gamma_{0ij0}$, or a pair $(u,v)$ with $u\le i\le j\le v$, with value $\gamma_{uijv}$, maximizing this value over all $i(M+1-j)+1$ options. Then
--
--   $$\gamma_o\ \ge\ \frac{d_{ij}}{i(M+1-j)+1}\ \ge\ \frac{d_{ij}}{(M+1)^2/4+1}.$$
--
--   The first constraint of (14) says that the values of all options sum to $d_{ij}$, so the largest is at least their average. In the proof of Theorem 4, with $d=\lambda^{[t,\theta T]}$, this gives the lower bound on RDP's chosen coordinate that drives (EC.28).
--
--   The printed bound has denominator $i^t(M+1-j^t)$, which omits the rejection option. It is false: for $M=N=1$, $T=2$, $C_{11}=1$, $p_{11}=1$, $\lambda^1_{11}=\lambda^2_{11}=1$, $\theta=1$, $t=1$ and request $1\to1$, one has $A_{11}=1$, $d_{11}=2$, and the unique optimal solution of (14)+(15) is $\gamma_{1111}=\gamma_{0110}=1$, whose maximal option has value $1<2=d_{11}/(1\cdot1)$. Theorem 4 is unaffected: only the constants of (EC.28)–(EC.29) change.
--
--   Differences from the source:
--   - correction: γ^{RDP,t}_{u^t i^t j^t v^t} = max_{(u,v)} γ ≥ λ^{[t,θT]}/(i^t(M+1−j^t)) ≥ λ^{[t,θT]}/((M+1)²/4) → the maximizing option (rejection included) has value ≥ d_ij/(i(M+1−j)+1) ≥ d_ij/((M+1)²/4+1); reason: the printed bound is false: M = N = 1, T = 2, C₁₁ = 1, p₁₁ = 1, λ¹₁₁ = λ²₁₁ = 1, θ = 1, t = 1, request 1→1 gives A₁₁ = 1, d₁₁ = 2 and the unique optimum γ₁₁₁₁ = γ₀₁₁₀ = 1 of (14)+(15), with maximum 1 < 2; the values of all i(M+1−j)+1 options, rejection included, sum to d_ij
--   - generalization: RDP's optimal solution γ^{RDP,t} of (14)+(15) with A = f(C^t) and d = λ^{[t,θT]} → any feasible solution γ of (14) for any A ∈ ℕ^{u≤v} and any d ≥ 0; reason: γ^{RDP,t} is such a solution; the bound uses only the first constraint of (14)
--   - encoding: the variables γ_{uijv} (u ≤ i ≤ j ≤ v) and γ_{0ij0} of (14)/(EC.18) → γ : ℕ×ℕ×ℕ×ℕ → ℝ, required to vanish outside the index set gammaIdx M; the reject variable is γ(0,i,j,0); reason: the other coordinates are not variables of the LP; fixing them to 0 changes no feasible objective value
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, proof of Theorem 4, p.ec23 (display after 'In time period t, after realization of (i^t, j^t)')

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_DynamicPrimal

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-- **Proof of Theorem 4, p.ec23, corrected** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*,
MSOM 2023, doi:10.1287/msom.2023.1188): "In time period t, after realization of `(iᵗ, jᵗ)`,
based on the maximum choice of `(uᵗ, vᵗ)` in RDP, we have
`γ^{RDP,t}_{uᵗiᵗjᵗvᵗ} = max_{(u,v)} γ^{RDP,t}_{uiᵗjᵗv} ≥ … = λ^{[t,θT]}_{iᵗjᵗ}/(iᵗ(M+1−jᵗ))
≥ λ^{[t,θT]}_{iᵗjᵗ}/((M+1)²/4)`."

The printed denominator `iᵗ(M+1−jᵗ)` counts only the pairs `(u, v)`; the maximum of Algorithm 3
also ranges over the rejection `[0, 0]`, whose coordinate `γ_{0iᵗjᵗ0}` enters the sum
`λ^{[t,θT]}_{iᵗjᵗ}` (first constraint of (14)). Corrected: the chosen coordinate is at least
`d_{ij} / (i(M+1−j) + 1)`, hence at least `d_{ij} / ((M+1)²/4 + 1)`.

**Formalization Note.** Stated for any right-hand sides `A ∈ ℕ^{u ≤ v}`, any demands `d ≥ 0`,
any itinerary `i ≤ j`, any feasible solution `γ` of (14) (RDP's optimal solution of (14)+(15) is
one) and any maximizing option `o` (a tie-break of Algorithm 3, line 4). -/
theorem rdp_choice_lower_bound {M : ℕ} (A : ℕ → ℕ → ℕ) (d : ℕ → ℕ → ℝ)
    (hd : ∀ ij ∈ itins M, 0 ≤ d ij.1 ij.2) (i j : ℕ) (hij : (i, j) ∈ itins M)
    (γ : Idx4 → ℝ) (hγ : IsFeasOPT M (fun u v => (A u v : ℝ)) d 0 γ)
    (o : Option (ℕ × ℕ)) (ho : IsMaxOption M γ i j o) :
    d i j / ((i * (M + 1 - j) + 1 : ℕ) : ℝ) ≤ optionValue γ i j o ∧
      d i j / (((M : ℝ) + 1) ^ 2 / 4 + 1) ≤ optionValue γ i j o := by sorry

end AssignToSeatRM
