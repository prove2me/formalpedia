-- Prove2me | Theorems.Thm_ColumnRandLP_proposition_EC_3
-- name    : ColumnRandLP.proposition_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:50.49144+00:00
-- url     : https://prove2.me/theorems/475ec233-97bd-43e6-a620-8c8dbaa80b8d
-- title:
--   Proposition EC.3 — w.p. $\ge1-\delta$, $P_J$ feasible ⇒ $\Delta v(P_J)\le\Delta v(P_{\mathrm{distr}})+\frac{C}{\sqrt K}(1+\|p\|_\infty m\|A\|_{\max})(1+\sqrt{2\log\frac2\delta})$, $p$ dual-optimal
-- statement:
--   Let $A$ be an $m\times n$ matrix with $\operatorname{rank}(A)=m$, $b\in\mathbb R^m$ and $c\in\mathbb R^n$ with $\|c\|_2=1$, such that the complete problem $P:\min\{c^Tx\mid Ax=b,\ x\ge0\}$ is feasible and bounded. Let $\xi$ be a probability distribution on $[n]$, $C$ a nonnegative constant, and
--   $$
--   P_{\mathrm{distr}}:\ \min\{c^Tx\mid Ax=b,\ 0\le x\le C\xi\}.
--   $$
--   Let $P_J$ be the column-randomized LP on a sample $J=(j_1,\dots,j_K)$, $K\ge1$, drawn i.i.d. from $\xi$, and $D_J$ its dual. For any $\delta\in(0,1)$, with probability at least $1-\delta$ over the sample $J$, the following holds: if $P_J$ is feasible, then
--   $$
--   \Delta v(P_J)\le\Delta v(P_{\mathrm{distr}})+\frac{C}{\sqrt K}\big(1+\|p\|_\infty\cdot m\cdot\|A\|_{\max}\big)\Big(1+\sqrt{2\log\tfrac2\delta}\Big)
--   $$
--   for every optimal solution $p$ of $D_J$. Here $\Delta v(P')=v(P')-v(P)$.
--
--   This is the dual-price form of the optimality-gap bound; Theorem 1 follows from it by choosing $p$ basic and bounding $\|p\|_\infty$ by $\gamma$.
--
--   **Formalization Note** The sample is `J : Fin K → Fin n` under `sampleMeasure ξ K`. The event is the implication "$P_J$ feasible $\Rightarrow$ the bound holds for every optimal $p$ of $D_J$", not a conditional probability. Optimal values are real infima; $P_{\mathrm{distr}}$ is assumed feasible. $C\ge0$ follows from that assumption and $\sum_j\xi_j=1$. $\log$ is natural.
--
--   Differences from the source:
--   - reading: the standing assumptions of §3.1 (‖c‖₂ = 1, P feasible and bounded, rank(A) = m) → hypotheses hc : ∑ c_j² = 1, IsBoundedBelow A b c, A.rank = m; P feasible is not separate because it follows from P_distr feasible; reason: §3.1 (p.6) states them once for the whole paper
--   - encoding: with probability at least 1 − δ over the sample J, if P_J is feasible then … → ENNReal.ofReal (1 − δ) ≤ ξ^{⊗K}{J | P_J feasible → ∀ p optimal for D_J, …} with J : Fin K → Fin n; reason: Appendix A (p.ec3) states the guarantee in this implication form, not as a conditional probability
--   - encoding: v(·) and P_distr possibly infeasible → real infima, with P_distr assumed feasible; reason: if P_distr is infeasible then Δv(P_distr) = +∞ and the paper's inequality is vacuous; otherwise every infimum used is the paper's minimum
--   - encoding: C a nonnegative constant → no separate hypothesis; reason: feasibility of P_distr and ∑ ξ_j = 1 force C ≥ 0
--   - reading: K, the number of samples → 1 ≤ K; reason: the bound contains 1/√K
--   - encoding: ‖p‖∞ = max_i |p_i|, ‖A‖max = max_ij |A_ij| → supNorm p = ⨆ i, |p i|, Amax A = ⨆ i, ⨆ j, |A i j|; reason: a supremum over a finite nonempty index type is the maximum; at m = 0, where the max is undefined, both are 0
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, Proposition EC.3, p.ec7 (proof pp.ec7–ec9); standing assumptions §3.1, p.6

import Mathlib
import Definitions.Def_ColumnRandLP_StandardLP
import Definitions.Def_ColumnRandLP_Norms
import Definitions.Def_ColumnRandLP_Model

open Matrix MeasureTheory

namespace ColumnRandLP

/-- **Proposition EC.3** (Akchen–Mišić, arXiv:2007.10461v5, Proposition EC.3, p.ec7; proof
pp.ec7–ec9). Let `C` be a nonnegative constant and `P_distr : min {cᵀx | Ax = b, 0 ≤ x ≤ Cξ}`.
Let `P_J` be the column-randomized LP solved by Algorithm 1. For any `δ ∈ (0,1)`, with
probability at least `1 − δ` over the sample `J`: if `P_J` is feasible, then
`Δv(P_J) ≤ Δv(P_distr) + C/√K · (1 + ‖p‖∞ · m · ‖A‖_max) · (1 + √(2 log(2/δ)))`
for any optimal solution `p` of the dual `D_J` of `P_J`.

**Formalization Note** Standing assumptions of §3.1 (p.6): `‖c‖₂ = 1` (`∑ c_j² = 1`), `P`
feasible and bounded below, `rank A = m`. Feasibility of `P` is not a separate hypothesis: it
follows from `hdistr`, since a feasible point of `P_distr` is feasible for `P`. The sample `J : Fin K → Fin n` (ordered, repeats
allowed) has law `ξ^{⊗K}` (`sampleMeasure`), `ξ ≥ 0`, `∑ ξ = 1`, `K ≥ 1`. The event is the
implication "P_J feasible → bound for every optimal `p` of `D_J`", not a conditional probability
(p.ec3). `v(·)` is a real infimum: `v(P)` is the true minimum by the standing assumptions, `v(P_J)`
whenever `P_J` is feasible, and `v(P_distr)` because `P_distr` is assumed feasible (`hdistr`);
when `P_distr` is infeasible, `Δv(P_distr) = +∞` and the claim is vacuous. `C ≥ 0` follows from
`hdistr` and `∑ ξ = 1`, so it is not a separate hypothesis. `log` is natural. -/
theorem proposition_EC_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hc : ∑ j, c j ^ 2 = 1) (hPbdd : IsBoundedBelow A b c)
    (hrank : A.rank = m)
    (ξ : Fin n → ℝ) (hξ0 : ∀ j, 0 ≤ ξ j) (hξ1 : ∑ j, ξ j = 1)
    (C : ℝ) (hdistr : (distrFeasSet A b C ξ).Nonempty)
    (K : ℕ) (hK : 1 ≤ K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleMeasure ξ K {J | IsFeasible (sampleMat A J) b →
        ∀ p, IsDualOptimal (sampleMat A J) b (sampleCost c J) p →
          vJ A b c J - lpValue A b c ≤
            vDistr A b c C ξ - lpValue A b c +
              C / Real.sqrt K * (1 + supNorm p * m * Amax A) *
                (1 + Real.sqrt (2 * Real.log (2 / δ)))} := by sorry

end ColumnRandLP
