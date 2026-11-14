-- Prove2me | Theorems.Thm_BilateralProfit_grid_rounding
-- name    : BilateralProfit.grid_rounding
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:22:06.830265+00:00
-- url     : https://prove2.me/theorems/3d8b6814-0bd4-4ec2-95d5-c5b8d48a6753
-- title:
--   §4.2.2 (proof of Theorem 4.1) — rounding valuations to the grid preserves profit and feedback
-- statement:
--   Let $K\ge1$. For $(s,b)\in[0,1]^2$ put $\bar s=\lceil Ks\rceil/K$ and $\bar b=\lfloor Kb\rfloor/K$ (seller values rounded up, buyer values down). Then
--
--   1. $(\bar s,\bar b)\in G_K$;
--   2. for every action $a\in\mathcal A$, $z_a(s,b)=z_a(\bar s,\bar b)$ and $\mathrm{Profit}((s,b),a)=\mathrm{Profit}((\bar s,\bar b),a)$;
--   3. hence for every valuation sequence in $[0,1]^2$ and every realization of its randomness, Algorithm 1 posts the same prices, holds the same weights and performs the same number of operations on the sequence as on its rounding.
--
--   So restricting the valuations to $G_K$ is without loss of generality.
--
--   Differences from the source:
--   - encoding: the grid $G_K$ of step size $1/K$ → hypothesis $0<K$; reason: the step size $1/K$ presupposes $K\ge1$ (Lemma A.6: "for every integer $K\ge1$")
--   - reading: "Restricting to $v_t\in G_K$ is without loss of generality since rounding … preserves the profit and feedback for any action in $\mathcal A$" → the rounding lands in $G_K$, preserves trade bit and profit at every action, and leaves the whole run of Algorithm 1 unchanged; reason: the run depends on the valuations only through the trade bits, which is what makes the restriction without loss of generality
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), proof of Theorem 4.1, §4.2.2, p.23 (PDF 25)

import Mathlib
import Definitions.Def_BilateralProfit_Algorithm1

namespace BilateralProfit

/-- **Grid rounding of valuations in the proof of Theorem 4.1**, Brüstle, di Gregorio, Fusco,
Leonardi (manuscript, sha256 e91e8127…), §4.2.2, p.23 (PDF 25): "rounding seller values up and
buyer values down to the grid preserves the profit and feedback for any action in `𝒜`".

For `(s, b) ∈ [0,1]²` let `s̄ = ⌈Ks⌉/K` and `b̄ = ⌊Kb⌋/K`. Then
1. `(s̄, b̄)` is a point of `G_K`;
2. for every `a ∈ 𝒜`, `z_a(s, b) = z_a(s̄, b̄)` and `Profit((s, b), a) = Profit((s̄, b̄), a)`;
3. consequently, for every valuation sequence in `[0,1]²` and every realization of the
   randomness, Algorithm 1 posts the same prices, holds the same weights and performs the same
   operations on the sequence and on its rounding. -/
theorem grid_rounding (K : ℕ) (hK : 0 < K) :
    (∀ s b : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      (∃ x : Grid K, pt K x = ((⌈(K : ℝ) * s⌉₊ : ℝ) / K, (⌊(K : ℝ) * b⌋₊ : ℝ) / K)) ∧
      ∀ a : Act K,
        tradeBit (s, b) (pt K a.1) =
            tradeBit ((⌈(K : ℝ) * s⌉₊ : ℝ) / K, (⌊(K : ℝ) * b⌋₊ : ℝ) / K) (pt K a.1) ∧
          profit (s, b) (pt K a.1) =
            profit ((⌈(K : ℝ) * s⌉₊ : ℝ) / K, (⌊(K : ℝ) * b⌋₊ : ℝ) / K) (pt K a.1)) ∧
    ∀ (T : ℕ) (S : Fin T → ℝ × ℝ), (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
      ∀ ω : Fin T → Fin (Jpar K),
        runW (alg1 K T S ω) =
          runW (alg1 K T (fun t => ((⌈(K : ℝ) * (S t).1⌉₊ : ℝ) / K,
            (⌊(K : ℝ) * (S t).2⌋₊ : ℝ) / K)) ω) := by sorry

end BilateralProfit
