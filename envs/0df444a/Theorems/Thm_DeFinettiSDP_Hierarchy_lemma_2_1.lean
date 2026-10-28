-- Prove2me | Theorems.Thm_DeFinettiSDP_Hierarchy_lemma_2_1
-- name    : DeFinettiSDP.Hierarchy.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:38.569989+00:00
-- url     : https://prove2.me/theorems/aa881e00-f9b7-4835-9d65-f5e8c1ba408f
-- title:
--   Lemma 2.1 (second inequality), p. 6 — symmetric cq-states: ∃ m < n, E‖ρ_{AZ_{m+1}|z} − ρ_{A|z} ⊗ ρ_{Z_{m+1}|z}‖₁² ≤ (2 ln 2) log d_A/n
-- statement:
--   Let $\rho_{AZ_1^n}=\sum_z|z\rangle\langle z|\otimes\tilde\rho(z)$ be a classical-quantum state on a $d_A$-dimensional quantum system $A$ and $n\ge1$ classical systems $Z_1,\dots,Z_n$ with a common finite alphabet, and suppose $\rho$ is invariant under every permutation of $Z_1,\dots,Z_n$: $\tilde\rho(z\circ\pi)=\tilde\rho(z)$ for all $\pi\in\mathfrak S_n$. Then there is $0\le m<n$ such that
--
--   $$\mathop{\mathbf E}_{z_1^m}\Big\{\big\|\rho_{AZ_{m+1}|z_1^m}-\rho_{A|z_1^m}\otimes\rho_{Z_{m+1}|z_1^m}\big\|_1^2\Big\}\ \le\ \frac{(2\ln2)\log d_A}{n},$$
--
--   where $\log$ is base 2, $\ln$ the natural logarithm, and the expectation is over the first $m$ outcomes $z_1^m$ drawn with their probabilities $p(z_1^m)$.
--
--   Conditioning on a few classical outcomes makes the next classical system almost independent of $A$. This is the decoupling step of the de Finetti theorem with linear constraints (Theorem 2.3).
--
--   **Formalization Note** The page's $n$ is `n + 1` here, so $0\le m<n$ reads `m ≤ n` and the bound has denominator $n+1$. The expectation is the sum over outcome strings $w$ of length $m$ weighted by $p(w)$; strings with $p(w)=0$ carry weight $0$. Only the second display of Lemma 2.1 (trace norm) is stated; the relative-entropy display is not formalized in this mission.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, Lemma 2.1 (second inequality), p. 6

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_DeFinettiSDP_Hierarchy_Conditional
open Matrix
open scoped ComplexOrder

namespace DeFinettiSDP.Hierarchy

/-- **Lemma 2.1, second inequality** (arXiv:1810.12197v3, p. 6). Let `ρ` be a classical-quantum
state on `A ⊗ Z₁ ⋯ Z_{n+1}` (the page's `n` is `n + 1` here), with the `Z`-systems classical
(alphabet `Fin t`), given by its blocks `ρ z ⪰ 0` with `∑_z Tr ρ z = 1`, and invariant under
every permutation of `Z₁, …, Z_{n+1}`. Then there is `0 ≤ m < n + 1` such that
`E_{z^m_1} ‖ρ_{A Z_{m+1}|z^m_1} − ρ_{A|z^m_1} ⊗ ρ_{Z_{m+1}|z^m_1}‖₁² ≤ (2 ln 2) log₂ d_A / (n + 1)`,
the expectation being over the first `m` outcomes with their probabilities. -/
theorem lemma_2_1 {dA t n : ℕ} (ρ : (Fin (n + 1) → Fin t) → Matrix (Fin dA) (Fin dA) ℂ)
    (hpos : ∀ z, (ρ z).PosSemidef) (htr : ∑ z, Matrix.trace (ρ z) = 1)
    (hsym : ∀ (π : Equiv.Perm (Fin (n + 1))) (z : Fin (n + 1) → Fin t), ρ (z ∘ π) = ρ z) :
    ∃ m : ℕ, m ≤ n ∧
      ∑ w : Fin m → Fin t, pZ ρ m w * (WildeQIT.traceNorm (condAZ ρ m w - prodAZ ρ m w)) ^ 2 ≤
        2 * Real.log 2 * Real.logb 2 (dA : ℝ) / ((n : ℝ) + 1) := by sorry

end DeFinettiSDP.Hierarchy
