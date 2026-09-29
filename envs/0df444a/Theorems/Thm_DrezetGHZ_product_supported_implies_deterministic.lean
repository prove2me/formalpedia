-- Prove2me | Theorems.Thm_DrezetGHZ_product_supported_implies_deterministic
-- name    : DrezetGHZ.product_supported_implies_deterministic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T20:29:05.010716+00:00
-- url     : https://prove2.me/theorems/004feae3-b55c-4573-9ac1-e3975ec2b877
-- title:
--   Eqs. (19)–(27): perfect GHZ correlations force local determinism
-- statement:
--   Let $p_1,p_2,p_3$ be probability distributions on $\{+1,-1\}$ (nonnegative, summing to $1$), and let $s\in\{\pm1\}$. Suppose that
--   $$p_1(\alpha)\,p_2(\beta)\,p_3(\gamma)=0\quad\text{whenever }\alpha\beta\gamma\neq s.$$
--   Then there are $a_1,a_2,a_3\in\{\pm1\}$ with $a_1a_2a_3=s$ such that each $p_j$ is the point mass at $a_j$: $p_j(\alpha)=1$ if $\alpha=a_j$, and $p_j(\alpha)=0$ otherwise.
--
--   This is the step in which locality combined with the perfect GHZ correlations yields determinism, $P_j(\alpha\mid\lambda,\hat n)=\delta_{\alpha,A_j(\lambda)}$ (Eq. (27)), applied at a fixed beable $\lambda$.
-- source:
--   A. Drezet, "An Elementary Proof That Everett's Quantum Multiverse Is Nonlocal: Bell-Locality and Branch-Symmetry in the Many-Worlds Interpretation", arXiv:2306.07794v1 [quant-ph] (2023), https://arxiv.org/abs/2306.07794, pp. 6–7, Eqs. (19)–(27).

import Mathlib

namespace DrezetGHZ
theorem product_supported_implies_deterministic (p₁ p₂ p₃ : ℤˣ → ℝ) (s : ℤˣ)
    (h₁ : ∀ α, 0 ≤ p₁ α) (h₂ : ∀ α, 0 ≤ p₂ α) (h₃ : ∀ α, 0 ≤ p₃ α)
    (hs₁ : ∑ α, p₁ α = 1) (hs₂ : ∑ α, p₂ α = 1) (hs₃ : ∑ α, p₃ α = 1)
    (hzero : ∀ α β γ : ℤˣ, α * β * γ ≠ s → p₁ α * p₂ β * p₃ γ = 0) :
    ∃ a₁ a₂ a₃ : ℤˣ, a₁ * a₂ * a₃ = s ∧
      (∀ α, p₁ α = if α = a₁ then 1 else 0) ∧
      (∀ α, p₂ α = if α = a₂ then 1 else 0) ∧
      (∀ α, p₃ α = if α = a₃ then 1 else 0) := by sorry
end DrezetGHZ
