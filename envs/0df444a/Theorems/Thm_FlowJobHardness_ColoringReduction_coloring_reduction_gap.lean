-- Prove2me | Theorems.Thm_FlowJobHardness_ColoringReduction_coloring_reduction_gap
-- name    : FlowJobHardness.ColoringReduction.coloring_reduction_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:33.006486+00:00
-- url     : https://prove2.me/theorems/32ffe73d-a08f-4aa3-b523-677942275059
-- title:
--   Completeness and soundness of the colouring reduction to generalized flow shops (core of Theorem 1.2)
-- statement:
--   Let $G=(V,E)$ be a simple graph on $n$ vertices whose vertices are partitioned into $d$ independent sets (a proper colouring into $d$ classes), let $r \ge 8$ be an integer, and let $S = S(r,d)$ be the generalized flow shop instance of the colouring reduction, with $\mathrm{lb} = r^{2d}$. Then:
--
--   1. **Structure.** $S$ is a generalized flow shop: every job visits its machines in strictly increasing global machine order. Every job has length $r^{2d}$ and every machine has load $r^{2d}$.
--   2. **Completeness.** For every $K\in\mathbb N$, if $G$ is $K$-colourable then
--   $$
--   C^*_{\max}(S) \le \mathrm{lb}\cdot 2K = 2K\, r^{2d},
--   $$
--   i.e. some feasible schedule of $S$ has makespan at most $2K\,r^{2d}$.
--   3. **Soundness.** For every real $L$ with $0 < L \le r$: if every independent set of $G$ has fewer than $n/(8L)$ vertices, then in every feasible schedule of $S$ fewer than half of the jobs finish within $L\cdot\mathrm{lb}$.
--
--   This gap is the mathematical core of Theorem 1.2 of the paper. Combined with Khot's hardness of distinguishing graphs of chromatic number at most $K$ from graphs with independence number at most $n/K^{(1/25)\log K}$, and with $d=\Delta+1$, $r = K^{(1/25)\log K}$, it shows that it is NP-hard to distinguish generalized flow shop instances with a schedule of makespan $2K\cdot\mathrm{lb}$ from those in which no schedule finishes more than half of the jobs within $\tfrac18 K^{(1/25)\log K}\cdot \mathrm{lb}$.
--
--   **Formalization Note.** Only the combinatorial gap is formalized; "NP-hard", "for sufficiently large $K$", "in time polynomial in $n$ and $r^d$", Khot's theorem and the parameter choice are not. The paper's soundness clause ("given a schedule where at least half the jobs finish within $\mathrm{lb}\cdot L$ time units, we can find an independent set of $G$ of size $n/(8L)$") is stated in its contrapositive, distinguishing form, as Theorem 1.2 uses it; its positive form is Lemma 3.9. "Sufficiently large $r$" is the explicit threshold $r\ge 8$. "At least half of the jobs" is $2\cdot\#\{j : C_j\le L\,r^{2d}\}\ge r^{2d}n$. The vertex set is `Fin n`, which covers every finite graph up to relabelling.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:12 (Section 3, completeness and soundness of the reduction), with Remark 3.6, Lemma 3.7 (p. 20:17) and Lemma 3.9 (p. 20:18); core of Theorem 1.2 (p. 20:5)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction
import Definitions.Def_FlowJobHardness_ColoringReduction_Schedule

open JobShopLTAS.Core

namespace FlowJobHardness.ColoringReduction

/-- **The completeness/soundness gap of the reduction `Γ`** (Mastrolilli–Svensson 2011, §3,
p. 20:12; Remark 3.6, Lemma 3.7 and Lemma 3.9, pp. 20:17–20:18), the mathematical core of
Theorem 1.2 (p. 20:5). For every graph `G` on `n` vertices with a proper colouring
`c : V → {1, …, d}` and every `r ≥ 8`, the instance `S = S(r, d)` satisfies:

* (a) `S` is a generalized flow shop: the machines of every job are visited in strictly
  increasing global machine order; every job length and every machine load equal
  `lb = r^{2d}`;
* (b) completeness: if `G` is `K`-colourable then `S` has a feasible schedule of makespan at
  most `2K · r^{2d}`;
* (c) soundness: for every real `0 < L ≤ r`, if every independent set of `G` has fewer than
  `n / (8L)` vertices, then in no feasible schedule of `S` do at least half of the jobs finish
  within `L · r^{2d}`. -/
theorem coloring_reduction_gap {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d))
    (r : ℕ) (hr : 8 ≤ r) :
    (∀ q : Fin (size r d n), ∀ i i' : Fin ((inst G c r).μ q), i < i' →
        MachBefore c ((inst G c r).π q i) ((inst G c r).π q i')) ∧
    (∀ q : Fin (size r d n), (inst G c r).jobLength q = (R r d : ℝ)) ∧
    (∀ p : Fin (size r d n), (inst G c r).load p = (R r d : ℝ)) ∧
    (∀ K : ℕ, G.Colorable K →
      ∃ s : (inst G c r).Op → ℝ,
        (inst G c r).IsFeasibleSchedule Finset.univ s ∧
        (inst G c r).makespan Finset.univ s ≤ 2 * (K : ℝ) * (R r d : ℝ)) ∧
    (∀ L : ℝ, 0 < L → L ≤ r →
      (∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → (I.card : ℝ) < (n : ℝ) / (8 * L)) →
      ∀ s : (inst G c r).Op → ℝ, (inst G c r).IsFeasibleSchedule Finset.univ s →
        2 * (finishedCount G c r s L : ℝ) < (size r d n : ℝ)) := by sorry

end FlowJobHardness.ColoringReduction
