-- Prove2me | Theorems.Thm_ColumnRandLP_theorem_1
-- name    : ColumnRandLP.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:54.845494+00:00
-- url     : https://prove2.me/theorems/c6ddfdda-86d3-41f3-8c9b-ada9dfa592f6
-- title:
--   Theorem 1 — w.p. $\ge1-\delta$, if $P_J$ is feasible, $\operatorname{rank}A_J=m$: $\Delta v(P_J)\le\Delta v(P_{\mathrm{distr}})+\frac{C(1+m\gamma\|A\|_{\max})}{\sqrt K}(1+\sqrt{2\log\frac2\delta})$
-- statement:
--   Let $A$ be an $m\times n$ matrix with $\operatorname{rank}(A)=m$, $b\in\mathbb R^m$ and $c\in\mathbb R^n$ with $\|c\|_2=1$, such that the complete problem
--   $$
--   P:\ \min\{c^Tx\mid Ax=b,\ x\ge0\}
--   $$
--   is feasible and bounded. Let $\xi$ be a probability distribution on $[n]$, let $C>0$, and define the distributional counterpart
--   $$
--   P_{\mathrm{distr}}:\ \min\{c^Tx\mid Ax=b,\ 0\le x\le C\cdot\xi\}.
--   $$
--   Let $J=(j_1,\dots,j_K)$, $K\ge1$, be $K$ indices drawn independently according to $\xi$, $A_J=[A_{j_1},\dots,A_{j_K}]$, and $P_J:\min\{c_J^T\tilde x\mid A_J\tilde x=b,\ \tilde x\ge0\}$ the column-randomized LP of Algorithm 1. Let $\gamma$ be an upper bound on $\|p\|_\infty$ for every basic solution $p$ of the dual $D:\max\{p^Tb\mid p^TA\le c^T\}$, and $\|A\|_{\max}=\max_{ij}|A_{ij}|$. Then for any $\delta\in(0,1)$, with probability at least $1-\delta$ over the sample $J$: if $P_J$ is feasible and $\operatorname{rank}(A_J)=m$, then
--   $$
--   \Delta v(P_J)\le\Delta v(P_{\mathrm{distr}})+\frac{C\,(1+m\gamma\|A\|_{\max})}{\sqrt K}\Big(1+\sqrt{2\log\tfrac2\delta}\Big),
--   $$
--   where $\Delta v(P')=v(P')-v(P)$ is the optimality gap.
--
--   The theorem bounds the optimality gap of solving an LP on $K$ randomly sampled columns by the gap of the distributional counterpart plus a term that decays like $1/\sqrt K$, independently of the number $n$ of columns.
--
--   **Formalization Note** Indices are 0-based and the sample is an ordered tuple `J : Fin K → Fin n` (repeats allowed) under the product law `sampleMeasure ξ K`; every probability vector $\xi$ is allowed, including ones with zero entries. The event is the implication "($P_J$ feasible and $\operatorname{rank}A_J=m$) $\Rightarrow$ bound", not a conditional probability. Optimal values are real infima and $P_{\mathrm{distr}}$ is assumed feasible. Basic solutions of $D$ range over every basis, feasible or not. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - reading: the standing assumptions of §3.1 (‖c‖₂ = 1, P feasible and bounded, rank(A) = m) → hypotheses hc : ∑ c_j² = 1, IsBoundedBelow A b c, A.rank = m; P feasible is not separate because it follows from P_distr feasible; reason: §3.1 (p.6) states them once for the whole paper
--   - encoding: with probability at least 1 − δ over the sample J, if P_J is feasible and rank(A_J) = m then … → ENNReal.ofReal (1 − δ) ≤ ξ^{⊗K}{J | P_J feasible ∧ rank A_J = m → …} with J : Fin K → Fin n; reason: Appendix A (p.ec3) states the guarantee in this implication form, not as a conditional probability; 0-based indices
--   - encoding: v(·) and P_distr possibly infeasible → real infima, with P_distr assumed feasible; reason: if P_distr is infeasible then Δv(P_distr) = +∞ and the paper's inequality is vacuous; otherwise every infimum used is the paper's minimum
--   - encoding: basic solution pᵀ = c_BᵀA_B⁻¹ of D for a basis B → IsBasicDualSolution, an injective β : Fin m → Fin n with linearly independent columns and pᵀA_{β k} = c_{β k}; reason: the same set of vectors p, written without the inverse
--   - reading: K, the number of samples → 1 ≤ K; reason: the bound contains 1/√K
--   - encoding: log → Real.log; reason: the natural logarithm, as in the McDiarmid bound behind (6)
--   - encoding: ‖p‖∞ = max_i |p_i|, ‖A‖max = max_ij |A_ij| → supNorm p = ⨆ i, |p i|, Amax A = ⨆ i, ⨆ j, |A i j|; reason: a supremum over a finite nonempty index type is the maximum; at m = 0, where the max is undefined, both are 0
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, Theorem 1, (5a)–(5c) and (6), p.7 (proof pp.ec7–ec9); standing assumptions §3.1, p.6; implication form Appendix A, p.ec3

import Mathlib
import Definitions.Def_ColumnRandLP_StandardLP
import Definitions.Def_ColumnRandLP_Norms
import Definitions.Def_ColumnRandLP_Model

open Matrix MeasureTheory

namespace ColumnRandLP

/-- **Theorem 1** (Akchen–Mišić, arXiv:2007.10461v5, Theorem 1, (6), p.7; proof pp.ec7–ec9).
Let `C` be a positive constant and `P_distr : min {cᵀx | Ax = b, 0 ≤ x ≤ C·ξ}` ((5a)–(5c)). Let
`P_J` be the column-randomized LP solved by Algorithm 1 and `A_J` its constraint matrix. For any
`δ ∈ (0,1)`, with probability at least `1 − δ` over the sample `J`: if `P_J` is feasible and
`rank(A_J) = m`, then
`Δv(P_J) ≤ Δv(P_distr) + C(1 + mγ‖A‖_max)/√K · (1 + √(2 log(2/δ)))`,
where `γ` is an upper bound on `‖p‖∞` for every basic solution `p` of the dual problem `D` and
`‖A‖_max = max_{ij} |A_{ij}|`.

**Formalization Note** Standing assumptions of §3.1 (p.6): `‖c‖₂ = 1` (`∑ c_j² = 1`), `P`
feasible and bounded below, `rank A = m`. Feasibility of `P` is not a separate hypothesis: it
follows from `hdistr`, since a feasible point of `P_distr` is feasible for `P`. Indices are 0-based (`Fin m`, `Fin n`, `Fin K`). The
sample `J : Fin K → Fin n` is an ordered tuple (repeats allowed) with law `ξ^{⊗K}`
(`sampleMeasure`), for any probability vector `ξ` (`ξ ≥ 0`, `∑ ξ = 1`; zero entries allowed),
and `K ≥ 1`. The event is the implication "(P_J feasible ∧ rank A_J = m) → bound", as Appendix A
(p.ec3) states; it is not a conditional probability. `v(·)` is a real infimum: `v(P)` is the
true minimum by the standing assumptions, `v(P_J)` whenever `P_J` is feasible, and `v(P_distr)`
because `P_distr` is assumed feasible (`hdistr`); when `P_distr` is infeasible,
`Δv(P_distr) = +∞` and the paper's inequality is vacuous. Basic solutions of `D` are
`IsBasicDualSolution` (every basis, feasible or not); `‖p‖∞ = supNorm p`,
`‖A‖_max = Amax A`. `log` is the natural logarithm. -/
theorem theorem_1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hc : ∑ j, c j ^ 2 = 1) (hPbdd : IsBoundedBelow A b c)
    (hrank : A.rank = m)
    (ξ : Fin n → ℝ) (hξ0 : ∀ j, 0 ≤ ξ j) (hξ1 : ∑ j, ξ j = 1)
    (C : ℝ) (hC : 0 < C) (hdistr : (distrFeasSet A b C ξ).Nonempty)
    (γ : ℝ) (hγ : ∀ p, IsBasicDualSolution A c p → supNorm p ≤ γ)
    (K : ℕ) (hK : 1 ≤ K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleMeasure ξ K {J | IsFeasible (sampleMat A J) b ∧ (sampleMat A J).rank = m →
        vJ A b c J - lpValue A b c ≤
          vDistr A b c C ξ - lpValue A b c +
            C * (1 + m * γ * Amax A) / Real.sqrt K *
              (1 + Real.sqrt (2 * Real.log (2 / δ)))} := by sorry

end ColumnRandLP
