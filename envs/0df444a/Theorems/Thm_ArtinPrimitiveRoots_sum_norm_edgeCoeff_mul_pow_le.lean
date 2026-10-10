-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_sum_norm_edgeCoeff_mul_pow_le
-- name    : ArtinPrimitiveRoots.sum_norm_edgeCoeff_mul_pow_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:23:52.549288+00:00
-- url     : https://prove2.me/theorems/ac76778b-76b5-41ca-a6a2-7a506a48767d
-- title:
--   [21] (4.25) — the weighted row sum of the ordered edge, with the fresh labels of the groups in C forced into a set V
-- statement:
--   Let $P$ be any parameters, $\omega$ a root of the box with $U, Y > 0$, $j$ an edge index, and assume $\nu_i(p) \ge 0$ on the group primes and $V_i \ge 1/2$. Let $C$ be a set of groups, $V$ a set of primes, $v_0 \ge 1$, and $s$ a state in `stSet` with memory size $|m|$. Then
--
--   $$\sum_{c \in \texttt{edgeChoices}} |\texttt{edgeCoeff}\ \omega\ j\ s\ c|\cdot\mathbf 1[\text{for } i \in C \text{ the label of group } i \text{ is fresh and in } V]\cdot v_0^{|m'|}$$
--
--   is at most
--
--   $$(1 + v_0)^K\cdot 16\bigl(1 + (10Y + 1)|\mathfrak M|\bigr)\prod_i\Bigl(\mathbf 1_{i \in C}\sum_{p \in \mathcal P_i \cap V}\nu_i(p) + \mathbf 1_{i \notin C}\bigl(\textstyle\sum_{p \in \mathcal P_i}\nu_i(p) + 2|m|\bigr)\Bigr)\,v_0^{|m|}.$$
--
--   Here $m'$ is the new memory and $|\mathfrak M|$ is the measure of `majorArcs x A₀ Y`.
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 24, (4.25).
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 24, (4.25)

import Mathlib
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMemoryModel

namespace ArtinPrimitiveRoots

open Finset MeasureTheory

set_option maxRecDepth 100000 in
theorem sum_norm_edgeCoeff_mul_pow_le (P : MemParams) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω)
    (hU : 0 < P.U) (hY : 0 < P.Y) (j : ℕ) (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p)
    (hV : ∀ i, 1 / 2 ≤ P.Vg i) (C : Finset (Fin P.K)) (Vs : Finset ℕ) {v₀ : ℝ} (hv₀ : 1 ≤ v₀)
    (s : P.MState) (hs : s ∈ P.stSet) :
    ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j s c‖ *
      (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs then 1 else 0) *
        v₀ ^ P.memSize (P.edgeOutMem s c) ≤
    (1 + v₀) ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
      (∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
        else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2)) * v₀ ^ P.memSize s.2.2 := by
  sorry

end ArtinPrimitiveRoots
