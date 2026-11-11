-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_theorem_2_2
-- name    : CosetTreeSVP.SVP.theorem_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:35:18.199832+00:00
-- url     : https://prove2.me/theorems/d25deccd-ef00-4ca7-93a8-88e1602565ff
-- title:
--   Theorem 2.2 — [ADRS15] discrete Gaussian sampler: M ≤ 2^{n/2} lattice vectors in time 2^{n/2+polylog(κ)+o(n)} and space 2^{n/2+o(n)}, exp(−Ω(κ))-close to i.i.d. D_{L,σ} above √2·η_{1/2}(L)
-- statement:
--   **Theorem 2.2** ([ADRS15, Theorem 5.11]). For every $c_0 > 0$ there are a program $P$ of the randomized rational RAM, constants $C, K \in \mathbb N$, $c_1 > 0$, a function $g$ with $g(n)/n \to 0$ and $n_0$ such that for all $n \ge n_0$, every nonsingular $B \in \mathbb Q^{n\times n}$ (basis of the full-rank lattice $L$), every rational $\sigma > 0$, every $\kappa \ge c_0 n$ and every $1 \le M \le 2^{n/2}$, on the input $(B, \sigma, \kappa, M)$ of bit length $\ell$:
--
--   - on every coin tape $P$ halts with $M$ lattice vectors (as integer coefficient vectors), within bit time $2^{n/2 + C(\log\kappa)^C + g(n)}(\ell+1)^K$ and bit space $2^{n/2+g(n)}(\ell+1)^K$;
--   - every output event is measurable, and if $\sigma > \sqrt2\,\eta_{1/2}(L)$, the output law is within statistical distance
--   $$\tfrac12\sum_o\big|\Pr[P\text{ outputs }o] - \Pr[(X_1,\dots,X_M)\text{ has word }o]\big| \le e^{-c_1\kappa}$$
--   of $M$ independent samples $X_1,\dots,X_M \sim D_{L,\sigma}$.
--
--   The algorithm samples the dual lattice at width $s$ in the SVP algorithm (Lemma 3.1 checks the width condition).
--
--   **Formalization Note.** Machine `TwMSOCount.Main`; input word `encDGS B σ κ M`; output `encSamples`; laws `outLaw`, `iidLaw`, distance `tvDist`.
--
--   Differences from the source:
--   - reading: κ = Ω(n) → ∀ c₀ > 0, the conclusion for every κ ≥ c₀·n, with constants chosen after c₀; reason: the stronger of the two readings of a hypothesis 'κ = Ω(n)'
--   - encoding: polylog(κ), o(n), exp(−Ω(κ)), n large → C·(log κ)^C with C ∈ ℕ, g with g(n)/n → 0, e^{−c₁κ} with c₁ > 0, n ≥ n₀, all before B, σ, κ, M; reason: the paper's convention (p. 11): n tends to infinity and every o, O, Ω is uniform over the parameters; the functions and constants are chosen after the fixed t and before n, the basis, d and v
--   - encoding: a classical algorithm with time and space in a real-arithmetic model ('polynomial factors in the bit length of the inputs', p. 11) → one program P of the randomized log-cost rational RAM TwMSOCount.Main, bit time and bit space on every coin tape, times (ℓ+1)^K for the input bit length ℓ; reason: the paper's cost convention (p. 11); exact real arithmetic is suppressed in the paper and is the solver's precision burden
--   - encoding: σ > 0 real; output 'lattice vectors' → σ rational (an input of the machine); integer coefficient vectors x with lattice vectors Bx; reason: a machine input must be finite; coefficient vectors determine the lattice vectors
--   - encoding: exp(−Ω(κ))-close → statistical distance ½Σ_o |μ(o) − ν(o)| over output words, plus measurability of each output event; reason: the standard total-variation distance on the countable output space
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 11 (PDF 13), Theorem 2.2

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_SolvesSVPWithin
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics
import Definitions.Def_CosetTreeSVP_SVP_Tree
import Definitions.Def_CosetTreeSVP_SVP_Algo

open MeasureTheory Filter Topology TwMSOCount.Main
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem theorem_2_2 (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ (P : Program) (C K : ℕ) (g : ℕ → ℝ) (c₁ : ℝ),
      Tendsto (fun n => g n / n) atTop (𝓝 0) ∧ 0 < c₁ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 → ∀ σ : ℚ, 0 < σ → ∀ κ M : ℕ,
        c₀ * n ≤ κ → 1 ≤ M → (M : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) →
        (∀ τ : ℕ → Bool, ∃ s : RunStats,
            runStats P τ (Config.init (encDGS B σ κ M)) = some s ∧
            (∃ x : Fin M → Fin n → ℤ, s.final.output = encSamples x) ∧
            (s.time : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 + C * Real.log κ ^ C + g n) *
              ((wordBits (encDGS B σ κ M) : ℝ) + 1) ^ K ∧
            (s.space : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 + g n) *
              ((wordBits (encDGS B σ κ M) : ℝ) + 1) ^ K) ∧
        (∀ o : List ℚ, MeasurableSet {τ | callOutput P (Config.init (encDGS B σ κ M)) τ = some o}) ∧
        (Real.sqrt 2 * RegevLWE.GaussConv.smoothingParam (latQ B) (1 / 2) < σ →
          tvDist (outLaw P (Config.init (encDGS B σ κ M))) (iidLaw B σ M) ≤
            ENNReal.ofReal (Real.exp (-(c₁ * κ)))) := by sorry

end CosetTreeSVP.SVP
