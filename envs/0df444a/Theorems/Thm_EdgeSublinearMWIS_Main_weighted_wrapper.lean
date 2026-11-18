-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_weighted_wrapper
-- name    : EdgeSublinearMWIS.Main.weighted_wrapper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T16:20:18.002739+00:00
-- url     : https://prove2.me/theorems/ff0061f6-d3f5-47bd-8ca3-7795d46cfbe2
-- title:
--   Polynomial finite-stack implementation of weighted preprocessing and projection
-- statement:
--   Let $U$ be any fixed finite deterministic stack program acting on unweighted graph inputs and returning a vertex mask followed by an encoded integer. There is a fixed finite deterministic stack program $P$ implementing the weighted reduction around $U$. Its polynomial overhead exponent $q>0$ is universal; its positive constant $K$ may depend on $U$.
--
--   For each graph, signed rational weight vector and rational $0<\varepsilon<1$, the program handles orders at most one directly by selecting nonnegative-weight vertices. At larger orders, if all clipped weights are zero, it returns the empty set. Otherwise let $\tau$ and $t_v$ be the scale and copy counts returned by the rounding routine applied to $w_v^+=\max\{w_v,0\}$, and write $N=\sum_v t_v$. If $U$ halts on that blow-up at accuracy $\varepsilon/2$, returning mask $J$ and integer $u$ in $T$ steps, then $P$ halts on the original weighted input and returns the mask of the owners represented in $J$, with time
--   $$s\le K\bigl(T+|\mathrm{input}|+N+1\bigr)^q.$$
--   The two direct branches have bound $K(|\mathrm{input}|+1)^q$.
--
--   This is a reusable implementation obligation for the p.20 weighted lifting. It assumes only the stated actual execution of $U$; neither an optimizer nor a correctness or resource field is supplied to either program. Arbitrary positive-denominator representations of every input rational are included.
-- source:
--   Bonnet and Chang, QPTAS for Max Weight Independent Set in Graphs with Strongly Edge-Sublinear Separators, STOC2027 submission #1044, p.20 proof of Theorem2: exact rational rounding, polynomially many copies, one unweighted call at epsilon/2, and projection to original vertices; signed preprocessing also covers the p.2 rational-weight domain. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_WeightedExecution
import Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts

namespace EdgeSublinearMWIS.Main

theorem weighted_wrapper :
    ∃ q : ℕ, 0 < q ∧ ∀ U : Program, ∃ (P : Program) (K : ℕ), 0 < K ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode),
        0 < ε.value → ε.value < 1 →
        (n ≤ 1 → ∃ s, Runs P (weightedInput G w ε) (mask (directVertices w)) s ∧
          s ≤ K * ((weightedInput G w ε).length + 1) ^ q) ∧
        (2 ≤ n → maximumWeight (clippedValues w) ≤ 0 →
          ∃ s, Runs P (weightedInput G w ε) (mask (∅ : Finset (Fin n))) s ∧
            s ≤ K * ((weightedInput G w ε).length + 1) ^ q) ∧
        (∀ (τ : ℚ) (t : Fin n → ℕ), 2 ≤ n →
          weightRounding (clippedValues w) ε.value = some (τ, t) →
          ∀ (J : Finset (Fin (totalCopies t))) (u T : ℕ),
            Runs U (unweightedInput (roundedGraph G t) (halfAccuracy ε))
              (mask J ++ encodeNat u) T →
            ∃ s, Runs P (weightedInput G w ε) (mask (originalVertices t J)) s ∧
              s ≤ K * (T + (weightedInput G w ε).length + totalCopies t + 1) ^ q) := by sorry

end EdgeSublinearMWIS.Main
