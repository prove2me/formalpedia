-- Prove2me | Theorems.Thm_DistMapClust_Main_theorem_1_9
-- name    : DistMapClust.Main.theorem_1_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:06:48.022259+00:00
-- url     : https://prove2.me/theorems/1f214fd2-f5eb-41e8-b4e2-5db796a8331d
-- title:
--   Theorem 1.9 — row-wise ordered norm mapping selection with types: a (1 + ε)-optimal selection in 2^{poly(d/ε)}·|I|^{O(1)} expected time
-- statement:
--   Given an instance $I$ of Row-Wise Ordered Norm Mapping Selection (points with types, arbitrary distance mappings, a row-wise ordered objective) and $\varepsilon>0$, one can find $\sigma:P\to[\psi]$ with $f(U(X,\sigma))\le(1+\varepsilon)\mathrm{OPT}_I$ in $2^{\mathrm{poly}(d/\varepsilon)}\cdot|I|^{O(1)}$ expected running time. Formally: for every class constant $c$ there are a program and universal $C,e$ such that for every instance, size parameter $s\ge n,k,d,\psi,\tau$ with $2^{-s^c}\le\mathrm{OPT}_I\le2^{s^c}$ and every $\varepsilon>0$, the run halts almost surely,
--   $$\mathbb E[\text{steps}]\le 2^{C(d/\varepsilon)^e+C}\cdot(Cs^e+C),$$
--   and every halting run outputs a valid selection of cost at most $(1+\varepsilon)\mathrm{OPT}_I$. It applies beyond clustering, e.g. to generalized load balancing with ordered norms, since $\delta$ need not be a metric.
--
--   **Formalization Note.** The expected number of steps is the lower integral of `steps` (`∞` on non-halting runs) against the tape law; the guarantee is required on every halting run (a Las Vegas algorithm).
--
--   Differences from the source:
--   - reading: Definition 1.8: 'f … be a row-wise monotone norm' → f = rowOrdNorm W f′, a row-wise ordered norm given by (W, f′); reason: obvious typo: the problem is named for ordered norms and §4 describes f through W and f′ (INSIGHTS I4)
--   - reading: an algorithm running in time … (bit model, §A.1; the Ball Intersection Algorithm 'supplied only as an oracle', §2.1) → one program of the unit-cost randomized oracle real RAM `DistMapClust_Main_Machine` (published SmaleNinth real-RAM core, uniform tape, no floor or other real-to-integer conversion, opaque point registers; one step per instruction including the oracles dist, ballInt, evalObj, evalNorm, evalMap, lam); reason: the paper fixes no machine; points of a possibly infinite F are reachable only through distances and the oracle (p. 8: the algorithm 'accesses only the distances')
--   - reading: 2^{poly(d/ε)} · |I|^{O(1)} expected running time → almost-sure halting, ∫⁻ steps ∂tapeLaw ≤ 2^{C·(d/ε)^e + C}·(C·s^e + C) with universal C, e, and the cost guarantee on every halting run; reason: expected time of a randomized algorithm that only returns a certified selection; explicit constants fixed before the instance
--   - reading: |I| and §A.1 assumption 3 → size parameter s ≥ n, k, d, ψ, τ and OptBounded s c OPT_I for a class constant c; reason: as for the clustering theorems; §A.1(3) is assumed for all instances
--   - encoding: distance mappings h_{t,ℓ}: R^k_{≥0} → R^d_{≥0} (arbitrary functions), δ: P × X → R≥0 → h : Fin τ → Fin ψ → (Fin k → ℝ) → (Fin d → ℝ) sending nonnegative vectors to nonnegative vectors, evaluated by a unit-cost oracle; δ as an n × k array of nonnegative reals in memory; reason: the centers enter only through their distances
--   - encoding: index sets [k], [d], [ψ], [n] (1-based) → Fin k, Fin d, Fin ψ, Fin n (0-based); P an injective family Fin n → α; reason: Lean convention; same instances
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 17, Theorem 1.9 (restated p. 46, proved p. 55)

import Mathlib
import Definitions.Def_DistMapClust_Main_IO

open MeasureTheory

namespace DistMapClust.Main

/-- Theorem 1.9 (p. 17; restated p. 46, proved p. 55). For every class constant `c` of §A.1(3)
there are one program and universal constants `C, e` such that on every instance of Row-Wise Ordered
Norm Mapping Selection, every size parameter `s ≥ n, k, d, ψ, τ` with `2^{-s^c} ≤ OPT_I ≤ 2^{s^c}`
and every `ε > 0`, the run on `(I, ε)` halts with probability one, its expected number of steps is at
most `2^{C (d/ε)^e + C} · (C s^e + C)`, and every halting run outputs a selection `σ : P → [ψ]` with
`f(U(X, σ)) ≤ (1 + ε) OPT_I`. -/
theorem theorem_1_9 :
    ∀ c : ℕ, ∃ prog : Program, Admissible prog ∧ ∃ C e : ℕ,
      ∀ (I : MapSelInstance) (s : ℕ), I.n ≤ s → I.k ≤ s → I.d ≤ s → I.ψ ≤ s → I.τ ≤ s →
      OptBounded s c I.OPT → ∀ ε : ℝ, 0 < ε →
        (∀ᵐ ν ∂tapeLaw, ∃ S, finalState prog I.oracles ν (I.start s ε) = some S) ∧
        ∫⁻ ν, steps prog I.oracles ν (I.start s ε) ∂tapeLaw ≤
          ENNReal.ofReal ((2 : ℝ) ^ ((C : ℝ) * ((I.d : ℝ) / ε) ^ e + C) *
            ((C : ℝ) * (s : ℝ) ^ e + C)) ∧
        ∀ (ν : Tape) (S : State Unit), finalState prog I.oracles ν (I.start s ε) = some S →
          ValidSel S I.n I.ψ ∧ I.cost (outSel S I.n I.ψ I.ψ_pos) ≤ (1 + ε) * I.OPT := by sorry

end DistMapClust.Main
