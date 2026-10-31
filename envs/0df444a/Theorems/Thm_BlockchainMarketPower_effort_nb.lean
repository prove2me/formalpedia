-- Prove2me | Theorems.Thm_BlockchainMarketPower_effort_nb
-- name    : BlockchainMarketPower.effort_nb
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:38.713838+00:00
-- url     : https://prove2.me/theorems/c7fe6dac-a32e-47fe-bb64-16fee14ad966
-- title:
--   Table of $e^*_{\mathcal{NB}}(\Psi,\Xi)$ (corrected: $\Psi=1$, $|\Xi|=2$)
-- statement:
--   Without blockchain, let $n=|\Xi|\ge1$ and $\Psi\ge0$. A number $e$ is a symmetric supplier effort if and only if one of the following holds:
--
--   1. $\Psi<1$, $n=1$ and $e=\Psi^2$;
--   2. $\Psi<1$, $n>1$ and $e=0$;
--   3. $\Psi\ge1$, $n=1$ and $e=1$;
--   4. $\Psi>1$, $n=2$ and $e\in\{0,1\}$;
--   5. $\Psi=1$, $n=2$ and $e\in[0,1]$ is arbitrary;
--   6. $\Psi\ge1$, $n>2$ and $e\in\{1,\ \Psi^{-2/(n-2)},\ 0\}$.
--
--   This is the complete solution of the suppliers' coordination problem without blockchain. It shows the multiplicity behind the selection printed in Proposition 3.1.
--
--   Differences from the source:
--   - correction: the table prints "1 or 0" for Ψ ≥ 1, |Ξ| = 2 → at Ψ = 1, |Ξ| = 2 every e ∈ [0, 1] is symmetric; "1 or 0" holds for Ψ > 1; reason: at |Ξ| = 2, Ψ = 1, e = 1/2 the profit u(e', 1/2) = √(e'/2) - e'/2 is maximized on [0, 1] at e' = 1/2, so e = 1/2 is a symmetric effort the table misses
--   - reading: §3.1: accept and effort are simultaneous and (2) depends on the accepting set Γ → symmetric fixed point with exponent |Ξ| - 1, assuming all of Ξ produce, then acceptance tested at that effort; reason: this is what the proof computes on pp.32, 36; the paper names no other solution of the supplier stage
--   - encoding: (1) with the factor Q → profit per unit, for every Ξ ≠ ∅; reason: the proof drops Q on p.32; nothing changes when Q > 0, and (1) is identically 0 when Q = 0
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, proof of Proposition 3.1, table of e∗_NB, p.33 (derivation pp.32–33)

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- The table of symmetric efforts without blockchain, Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580,
proof of Proposition 3.1, table of `e∗_NB`, p.33 (derivation pp.32–33), **corrected at `Ψ = 1`,
`|Ξ| = 2`**, where every `e ∈ [0, 1]` is a symmetric effort; the page prints "1 or 0".

**Formalization Note.** The middle root is `Real.rpow`, and the hypothesis `1 ≤ n` makes `n - 1` in
`noRecallProb` untruncated. -/
theorem effort_nb (n : ℕ) (hn : 1 ≤ n) (Ψ : ℝ) (hΨ : 0 ≤ Ψ) (e : ℝ) :
    IsSymEffort .NB n Ψ e ↔
      (Ψ < 1 ∧ n = 1 ∧ e = Ψ ^ 2) ∨
      (Ψ < 1 ∧ 1 < n ∧ e = 0) ∨
      (1 ≤ Ψ ∧ n = 1 ∧ e = 1) ∨
      (1 < Ψ ∧ n = 2 ∧ (e = 1 ∨ e = 0)) ∨
      (Ψ = 1 ∧ n = 2 ∧ e ∈ Set.Icc (0 : ℝ) 1) ∨
      (1 ≤ Ψ ∧ 2 < n ∧ (e = 1 ∨ e = Ψ ^ (-2 / ((n : ℝ) - 2)) ∨ e = 0)) := by sorry

end BlockchainMarketPower
