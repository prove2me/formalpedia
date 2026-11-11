-- Prove2me | Theorems.Thm_DistMapClust_Main_theorem_1_4
-- name    : DistMapClust.Main.theorem_1_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:06:53.994195+00:00
-- url     : https://prove2.me/theorems/af7f827e-22d9-4f81-927d-9ea0c08fe3f9
-- title:
--   Theorem 1.4 — row-wise ordered norm mapping selection: a (1 + ε)-optimal selection in 2^{poly(d/ε)}·|I|^{O(1)} expected time
-- statement:
--   Given an instance $I$ of Row-Wise Ordered Norm Linear Mapping Selection (Definition 1.3: one fixed tuple of centers, distances not necessarily metric, distance mappings $h_\ell:\mathbb R^k_{\ge0}\to\mathbb R^d_{\ge0}$, a row-wise ordered objective) and $\varepsilon>0$, one can find $\sigma:P\to[\psi]$ with $\mathrm{cost}_I(\sigma)\le(1+\varepsilon)\mathrm{OPT}_I$ in $2^{\mathrm{poly}(d/\varepsilon)}\cdot|I|^{O(1)}$ expected running time. Formally: for every class constant $c$ there are a program and universal $C,e$ such that for every instance with one point type, size parameter $s\ge n,k,d,\psi$ with $2^{-s^c}\le\mathrm{OPT}_I\le2^{s^c}$ and every $\varepsilon>0$, the run halts almost surely,
--   $$\mathbb E[\text{steps}]\le 2^{C(d/\varepsilon)^e+C}\cdot(Cs^e+C),$$
--   and every halting run outputs a valid selection of cost at most $(1+\varepsilon)\mathrm{OPT}_I$. It is the selection half of the goal.
--
--   **Formalization Note.** Definition 1.3 is `MapSelInstance` with `τ = 1`.
--
--   Differences from the source:
--   - reading: an algorithm running in time … (bit model, §A.1; the Ball Intersection Algorithm 'supplied only as an oracle', §2.1) → one program of the unit-cost randomized oracle real RAM `DistMapClust_Main_Machine` (published SmaleNinth real-RAM core, uniform tape, no floor or other real-to-integer conversion, opaque point registers; one step per instruction including the oracles dist, ballInt, evalObj, evalNorm, evalMap, lam); reason: the paper fixes no machine; points of a possibly infinite F are reachable only through distances and the oracle (p. 8: the algorithm 'accesses only the distances')
--   - reading: 2^{poly(d/ε)} · |I|^{O(1)} expected running time → almost-sure halting, ∫⁻ steps ∂tapeLaw ≤ 2^{C·(d/ε)^e + C}·(C·s^e + C) with universal C, e, and the cost guarantee on every halting run; reason: expected time of a randomized algorithm that only returns a certified selection; explicit constants fixed before the instance
--   - reading: |I| and §A.1 assumption 3 → size parameter s ≥ n, k, d, ψ and OptBounded s c OPT_I for a class constant c; reason: as for the clustering theorems; §A.1(3) is assumed for all instances
--   - encoding: Definition 1.3's instance (P, X, δ, f, H), H = {h_ℓ} a set of functions → MapSelInstance with τ = 1: δ as an n × k array of nonnegative reals, h 0 ℓ arbitrary functions sending nonnegative vectors to nonnegative vectors, f = rowOrdNorm W f′; reason: Definition 1.8 with a single type is Definition 1.3
--   - encoding: index sets [k], [d], [ψ], [n] (1-based) → Fin k, Fin d, Fin ψ, Fin n (0-based); P an injective family Fin n → α; reason: Lean convention; same instances
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 8, Theorem 1.4

import Mathlib
import Definitions.Def_DistMapClust_Main_IO

open MeasureTheory

namespace DistMapClust.Main

/-- Theorem 1.4 (p. 8). For every class constant `c` of §A.1(3) there are one program and universal
constants `C, e` such that on every instance of Row-Wise Ordered Norm Linear Mapping Selection (one
point type, `τ = 1`), every size parameter `s ≥ n, k, d, ψ` with `2^{-s^c} ≤ OPT_I ≤ 2^{s^c}` and
every `ε > 0`, the run on `(I, ε)` halts with probability one, its expected number of steps is at most
`2^{C (d/ε)^e + C} · (C s^e + C)`, and every halting run outputs a selection `σ : P → [ψ]` with
`cost_I(σ) ≤ (1 + ε) OPT_I`. -/
theorem theorem_1_4 :
    ∀ c : ℕ, ∃ prog : Program, Admissible prog ∧ ∃ C e : ℕ,
      ∀ (I : MapSelInstance), I.τ = 1 → ∀ s : ℕ, I.n ≤ s → I.k ≤ s → I.d ≤ s → I.ψ ≤ s →
      OptBounded s c I.OPT → ∀ ε : ℝ, 0 < ε →
        (∀ᵐ ν ∂tapeLaw, ∃ S, finalState prog I.oracles ν (I.start s ε) = some S) ∧
        ∫⁻ ν, steps prog I.oracles ν (I.start s ε) ∂tapeLaw ≤
          ENNReal.ofReal ((2 : ℝ) ^ ((C : ℝ) * ((I.d : ℝ) / ε) ^ e + C) *
            ((C : ℝ) * (s : ℝ) ^ e + C)) ∧
        ∀ (ν : Tape) (S : State Unit), finalState prog I.oracles ν (I.start s ε) = some S →
          ValidSel S I.n I.ψ ∧ I.cost (outSel S I.n I.ψ I.ψ_pos) ≤ (1 + ε) * I.OPT := by sorry

end DistMapClust.Main
