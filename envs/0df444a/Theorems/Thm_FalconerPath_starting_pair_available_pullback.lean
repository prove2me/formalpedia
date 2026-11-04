-- Prove2me | Theorems.Thm_FalconerPath_starting_pair_available_pullback
-- name    : FalconerPath.starting_pair_available_pullback
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:42.189979+00:00
-- url     : https://prove2.me/theorems/ccb9f532-0a2c-4779-b727-767805a895fa
-- title:
--   Directional availability lifts to the original space
-- statement:
--   Let $1\le m\le d$ be integers and let $P:\mathbb R^d\to\mathbb R^m$ be continuous linear with $PP^*=I$. Let $\nu,\rho$ be probabilities such that both their original support pair and the support pair of $P_\#\nu,P_\#\rho$ are bounded and positively separated. Let $G_N$ be Borel pair relations in $\mathbb R^m$ and let $q\ge0$. If $q$ is available for $G_N$ with the projected laws, then $q$ is available for $H_N=(P\times P)^{-1}(G_N)$ with the original laws.
--
--   For either family, availability means that for every $e>0$ there are $c,C>0$ and $N_0$ such that every $N\ge N_0$ admits a Borel exceptional subrelation of product mass at most $C2^{-cN}$, after whose removal both unnormalized directional laws assign mass at most $2^{eN}u^q$ to every radius-$u$ cap, $2^{-N}\le u\le1$, at almost every corresponding pin. The Lean statement isolates availability pullback, including exceptional-set mass and absorption of fixed cap constants, without any partition assertion.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.4, Proposition 5.10 (Starting pair measures), label prep:starting-pairs, even-dimensional proof paragraph at “lifting to the original space”, odd-dimensional paragraph at “Lift the resulting cap bounds and the exceptional pair sets”, and final paragraph at “Pullback preserves product masses”.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem starting_pair_available_pullback {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (P : Space d →L[ℝ] Space m) (hP : OrthogonalSurjection P)
    (ν ρ : Measure (Space d)) (hν : Probability ν) (hρ : Probability ρ)
    (hsep : HasBoundedSeparated ν ρ)
    (hprojsep : HasBoundedSeparated (Measure.map P ν) (Measure.map P ρ))
    (G : ℕ → PairSet m) (hG : ∀ N, MeasurableSet (G N))
    (q : ℝ) (hq : 0 ≤ q) (hav : Available (Measure.map P ν) (Measure.map P ρ) G q) :
    Available ν ρ (fun N => (fun z : Space d × Space d => (P z.1,P z.2)) ⁻¹' G N) q := by sorry
end FalconerPath
