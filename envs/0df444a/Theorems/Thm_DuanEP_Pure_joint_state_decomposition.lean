-- Prove2me | Theorems.Thm_DuanEP_Pure_joint_state_decomposition
-- name    : DuanEP.Pure.joint_state_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:26.421573+00:00
-- url     : https://prove2.me/theorems/2654163e-67c0-499f-ba7f-18671b263d74
-- title:
--   Eqs. (2)–(3): decomposition of $m$ squeezed pairs into the states $|j\rangle$, and $f_j^{(m)}=(j+m-1)!/(j!(m-1)!)$
-- statement:
--   Let $m\ge 1$, $r\in\mathbb R$ and $\lambda=\tanh r$. Then:
--
--   1. the joint state of the $m$ pairs decomposes as in Eq. (2),
--   $$
--   |\Psi\rangle_{(A_iB_i)}=(1-\lambda^2)^{m/2}\sum_{j=0}^{\infty}\lambda^j\sqrt{f_j^{(m)}}\;|j\rangle_{(A_iB_i)},
--   $$
--   with the series converging at every Fock label $(a,b)$;
--   2. each state $|j\rangle_{(A_iB_i)}$ of Eq. (3) is normalized;
--   3. $f_j^{(m)}$ is the number of $m$-tuples $(i_1,\dots,i_m)$ of nonnegative integers with $i_1+\dots+i_m=j$, and
--   $$
--   f_j^{(m)}=\frac{(j+m-1)!}{j!\,(m-1)!}.
--   $$
--
--   The decomposition (2) is what makes a measurement of the total excitation number on one side leave a maximally entangled state.
--
--   **Formalization Note** $(1-\lambda^2)^{m/2}$ is written $(\sqrt{1-\lambda^2})^m$, equal because $1-\lambda^2>0$. Eq. (2) is stated coefficientwise, as a convergent series over $j$ at each label.
--
--   Differences from the source:
--   - generalization: squeezing parameter r ≥ 0 (implicit) → every real r; reason: for r < 0, tanh r = −tanh|r| and the state is the |r| state up to the local phase (−1)^n on the B modes; the statement at r ≥ 0 is the paper's
--   - encoding: m entangled pairs, i = 1, …, m → hypothesis 1 ≤ m; reason: the paper's setting has at least one pair; f_j^{(m)} = (j+m−1)!/(j!(m−1)!) is undefined at m = 0
--   - encoding: (1 − λ²)^{m/2} → (√(1 − λ²))^m; reason: equal since 1 − λ² > 0
--   - encoding: vector identity (2) in Fock space → coefficientwise HasSum over j at each label (a, b); reason: a state is its coefficient function; at each label only one j contributes
--   - generalization: f_j^{(m)} given by its factorial formula → also: f_j^{(m)} is the number of m-tuples with sum j; reason: this count is the normalization constant of (3) that the paper uses implicitly; the factorial formula is still asserted
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, pp. 1–2, Eqs. (2), (3) and the formula for f_j^(m)

import Mathlib
import Definitions.Def_DuanEP_Pure_jointCoeff
import Definitions.Def_DuanEP_Pure_outcomeState

open Nat

namespace DuanEP.Pure

/-- Eqs. (2)–(3) and the value of `f_j^{(m)}` (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, pp. 1–2): for `m ≥ 1` pairs,
1. `|Ψ⟩_{(AᵢBᵢ)} = (1 − λ²)^{m/2} ∑_j λ^j √(f_j^{(m)}) |j⟩_{(AᵢBᵢ)}` coefficientwise, with `λ = tanh r`;
2. each `|j⟩_{(AᵢBᵢ)}` is normalized;
3. `f_j^{(m)}` is the number of `m`-tuples of occupations with sum `j` and equals
   `(j + m − 1)! / (j! (m − 1)!)`.

**Formalization Note** `(1 − λ²)^{m/2}` is written `(√(1 − λ²))^m`, equal since `1 − λ² > 0`.
The hypothesis `1 ≤ m` is the paper's setting of `m` pairs; the factorial formula is undefined at
`m = 0`. Every real `r`. -/
theorem joint_state_decomposition (m : ℕ) (hm : 1 ≤ m) (r : ℝ) :
    (∀ p : (Fin m → ℕ) × (Fin m → ℕ),
      HasSum (fun j : ℕ => (((Real.sqrt (1 - Real.tanh r ^ 2)) ^ m * Real.tanh r ^ j *
          Real.sqrt (fCount m j) : ℝ) : ℂ) * outcomeState m j p) (jointCoeff m r p)) ∧
    (∀ j : ℕ, HasSum (fun p : (Fin m → ℕ) × (Fin m → ℕ) => ‖outcomeState m j p‖ ^ 2) 1) ∧
    (∀ j : ℕ, (Finset.Nat.antidiagonalTuple m j).card = fCount m j ∧
      (fCount m j : ℝ) = ((j + m - 1)! : ℝ) / ((j ! : ℝ) * ((m - 1)! : ℝ))) := by sorry

end DuanEP.Pure
