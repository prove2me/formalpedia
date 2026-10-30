-- Prove2me | Theorems.Thm_CompOT_SinkhornConv_proposition_4_3_unique_scaling_form
-- name    : CompOT.SinkhornConv.proposition_4_3_unique_scaling_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:21:48.829273+00:00
-- url     : https://prove2.me/theorems/64cabaad-ce15-4d29-98de-09c320d13e92
-- title:
--   Proposition 4.3: entropic OT has a unique solution, of the form $P_{i,j} = u_i K_{i,j} v_j$
-- statement:
--   Let $a\in\Sigma_n$ and $b\in\Sigma_m$ be histograms (nonnegative entries summing to $1$; zero entries allowed), let $C\in\mathbb R^{n\times m}$ be any cost matrix, let $\varepsilon>0$ and let $K_{i,j} = e^{-C_{i,j}/\varepsilon}$ be the Gibbs kernel. Then the entropic optimal transport problem
--   $$\min_{P\in U(a,b)} \ \langle P, C\rangle - \varepsilon H(P) \tag{4.2}$$
--   has a solution $P$, every solution equals $P$, and there are nonnegative vectors $u\in\mathbb R^n_+$, $v\in\mathbb R^m_+$ with
--   $$P_{i,j} = u_i\,K_{i,j}\,v_j \qquad \text{for all } i, j. \tag{4.12}$$
--
--   The scaling form reduces entropic optimal transport to the matrix scaling problem $u\odot(Kv)=a$, $v\odot(K^\top u)=b$, which Sinkhorn's algorithm solves.
--
--   **Formalization Note** A solution of (4.2) is a coupling at which the objective attains its minimum over $U(a,b)$ (`IsMinOn` together with membership). The entropy uses $0\log 0 = 0$.
--
--   Differences from the source:
--   - reading: H(P) with the convention H = −∞ stated for vectors with a zero entry → entropy with 0·log 0 = 0 (Real.log 0 = 0); reason: the −∞ convention is stated for vectors; applied to matrices it would make every coupling with a zero entry infeasible, which is impossible to avoid when a or b has a zero entry; 0 log 0 = 0 is the continuous extension of x(log x − 1)
--   - encoding: "the solution to (4.2) is unique" → ∃ P ∈ U(a,b) minimizing the objective on U(a,b), and every minimizer in U(a,b) equals P; reason: existence and uniqueness of the minimizer, stated with IsMinOn plus membership
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.2, Proposition 4.3, eq. (4.12), p. 432

import Mathlib
import Definitions.Def_CompOT_SinkhornConv_couplings
import Definitions.Def_CompOT_SinkhornConv_entropicObjective
import Definitions.Def_CompOT_SinkhornConv_gibbsKernel

open Matrix

namespace CompOT.SinkhornConv

/-- **Proposition 4.3: the solution of (4.2) is unique and has the scaling form (4.12).**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), §4.2, Proposition 4.3, p. 432: "The solution to (4.2) is unique and has the form
∀(i, j) ∈ JnK × JmK, Pi,j = uiKi,jvj (4.12) for two (unknown) scaling variable (u, v) ∈ Rn+ × Rm+."

Let `a ∈ Σ_n`, `b ∈ Σ_m` (nonnegative, summing to `1`), let `C` be any real `n × m` cost matrix
and `ε > 0`. Then problem (4.2), `min_{P ∈ U(a,b)} ⟨P, C⟩ − ε H(P)`, has a solution `P`, every
solution equals `P`, and `P_{i,j} = x_i K_{i,j} y_j` for some nonnegative vectors `x ∈ ℝⁿ₊`,
`y ∈ ℝᵐ₊`, where `K = gibbsKernel C ε`.

**Formalization Note.** "The solution … is unique" is read as existence plus uniqueness of a
minimizer of `entropicObjective C ε` over `couplings a b`; a minimizer is a member of the set at
which `IsMinOn` holds (membership is stated, so `IsMinOn` is not vacuous). The entries of `a` and
`b` may vanish (`Σ_n` is the closed simplex), and the scalings are then only nonnegative, as in
the paper's `ℝⁿ₊ × ℝᵐ₊`. The entropy uses `0 log 0 = 0`. -/
theorem proposition_4_3_unique_scaling_form {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1) (hb : ∀ j, 0 ≤ b j) (hb1 : ∑ j, b j = 1)
    (C : Matrix (Fin n) (Fin m) ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Matrix (Fin n) (Fin m) ℝ,
      (P ∈ couplings a b ∧ IsMinOn (entropicObjective C ε) (couplings a b) P) ∧
      (∀ Q, Q ∈ couplings a b → IsMinOn (entropicObjective C ε) (couplings a b) Q → Q = P) ∧
      ∃ x : Fin n → ℝ, ∃ y : Fin m → ℝ, (∀ i, 0 ≤ x i) ∧ (∀ j, 0 ≤ y j) ∧
        ∀ i j, P i j = x i * gibbsKernel C ε i j * y j := by sorry

end CompOT.SinkhornConv
