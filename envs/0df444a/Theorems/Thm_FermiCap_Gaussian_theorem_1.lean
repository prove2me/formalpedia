-- Prove2me | Theorems.Thm_FermiCap_Gaussian_theorem_1
-- name    : FermiCap.Gaussian.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:02.52383+00:00
-- url     : https://prove2.me/theorems/bb76f534-05bb-418b-924d-d2521108940a
-- title:
--   Theorem 1 — Gaussian capacity and one-shot equality for n ≤ 2
-- statement:
--   Let $n\ge1$, let every attenuation $b_p$ of the fermionic product channel $\Phi_b$ lie in $[0,1]$, and write $b_1^\downarrow\ge\cdots\ge b_{2n}^\downarrow$ for the coefficients in decreasing order. Then
--   $$C_1^g(\Phi_b)=n-H\left(\frac{1+b_1^\downarrow}{2}\right)-\sum_{j=1}^{n-1}H\left(\frac{1+b_{2j}^\downarrow b_{2j+1}^\downarrow}{2}\right).$$
--   Moreover, for $n\le2$, the one-shot capacity over all finite output ensembles agrees with the Gaussian capacity:
--   $$C_1(\Phi_b)=C_1^g(\Phi_b).$$
--   This is the paper's central formula and its low-dimensional unrestricted-capacity result.
--
--   **Formalization Note** The Lean statement quantifies over every $b$ and every permutation sorting it; it does not require the input attenuation vector to be sorted.
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 2, Theorem 1 and eq. (6)

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Capacity

noncomputable section

namespace FermiCap.Gaussian

/-- Theorem 1: the formula for every attenuation vector, expressed using any
decreasing rearrangement, together with C₁=C₁ᵍ for one and two qubits. -/
theorem theorem_1 (n : ℕ) (b : Fin (2 * n) → ℝ) (σ : Equiv.Perm (Fin (2 * n)))
    (hn : 1 ≤ n) (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1)
    (hsort : Antitone (b ∘ σ)) :
    gaussCap n (channel n b) = (n : ℝ) - gaussFormula n hn (b ∘ σ) ∧
      (n ≤ 2 → oneShotCap n (channel n b) = gaussCap n (channel n b)) := by sorry

end FermiCap.Gaussian
