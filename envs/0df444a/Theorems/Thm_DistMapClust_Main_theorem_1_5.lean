-- Prove2me | Theorems.Thm_DistMapClust_Main_theorem_1_5
-- name    : DistMapClust.Main.theorem_1_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:06:37.650599+00:00
-- url     : https://prove2.me/theorems/b8d8f6f1-366a-45b4-a72d-856c09a87726
-- title:
--   Theorem 1.5 — a (1 + χ + ε)-approximation in time ζ(k, d, ψ, 1/ε, λ(ε/100))·poly(|I|) for linear distance mappings and row-wise ordered norms
-- statement:
--   Let $\lambda:\mathbb R_{\ge0}\to\mathbb N$ and $\chi\in[0,2]$, and let $\mathfrak I$ be a class of instances of k-Clustering with Linear Distance Mappings whose metrics, with their Ball Intersection oracles, have $\chi$-shifted algorithmic $\varepsilon$-scatter dimension $\lambda(\cdot)$, whose objectives are row-wise ordered norms, and which satisfy §A.1(3) with constant $c$. Then there are one program, a function $\zeta$ and constants $C,e$ such that for every $I\in\mathfrak I$, every size parameter $s\ge n,k,d,\psi$ with $2^{-s^c}\le\mathrm{OPT}_I\le2^{s^c}$ and every $\varepsilon\in(0,1/48)$, every run on $(I,\chi,\varepsilon)$ halts within $\zeta(k,d,\psi,1/\varepsilon,\lambda(\varepsilon/100))\cdot(Cs^e+C)$ steps and outputs $X\in F^k$ and $\sigma:P\to[\psi]$, and
--   $$\Pr\big[f(U(X,\sigma))>(1+\chi+\varepsilon)\,\mathrm{OPT}_I\big]\le 1/n .$$
--   This is the paper's main algorithmic result: an EPAS ($\chi=0$) for every class of bounded algorithmic scatter dimension, and a $(3+\varepsilon)$-approximation in FPT time for all finite metrics ($\chi=2$, Lemma 2.6), for k-median, k-means, k-center, min-sum of radii, their fault-tolerant, capacitated, penalty and outlier variants and more, with one algorithm that accesses the metric only through distances.
--
--   **Formalization Note.** `ζ : ℕ → ℕ → ℕ → ℝ → ℕ → ℝ` is arbitrary. The probability clause bounds the tape measure of the failure set by $1/n$. Outputs: $x_i$ in point cell $-1-i$ and $\sigma(p)$ in integer cell $-1-p$, valid on every run.
--
--   Differences from the source:
--   - reading: an algorithm running in time … (bit model, §A.1; the Ball Intersection Algorithm 'supplied only as an oracle', §2.1) → one program of the unit-cost randomized oracle real RAM `DistMapClust_Main_Machine` (published SmaleNinth real-RAM core, uniform tape, no floor or other real-to-integer conversion, opaque point registers; one step per instruction including the oracles dist, ballInt, evalObj, evalNorm, evalMap, lam); reason: the paper fixes no machine; points of a possibly infinite F are reachable only through distances and the oracle (p. 8: the algorithm 'accesses only the distances')
--   - reading: poly(|I|), |I| the bit size, and §A.1 assumption 3: 2^{−poly(|I|)} ≤ OPT_I ≤ 2^{poly(|I|)} → a size parameter s given as input with n, k, d, ψ ≤ s; poly(|I|) = C·s^e + C with universal C, e fixed before the instance; hypothesis OptBounded s c OPT_I (2^{−s^c} ≤ OPT_I ≤ 2^{s^c}) for a class constant c quantified before the program; reason: the bit size of an instance with opaque points and infinite F has no meaning on a real RAM; §A.1(3) is a standing assumption for all instances
--   - reading: with high probability → the tape measure of the failure set is at most 1/n (an outer-measure upper bound); reason: 1/n is the value the proof of Theorem 1.2 establishes (p. 45: '(1 − p)^{(log2 n)/p} ≤ (1/2)^{log2 n} ≤ 1/n')
--   - generalization: a class M of metric spaces with one Ball Intersection Algorithm C_M (polynomial time) of χ-shifted algorithmic ε-scatter dimension λ(·) → each instance carries its own Ball Intersection oracle C (Definition 2.2 clauses 1–2, no running-time requirement); the hypothesis is that every instance's (P, F, δ, C) has χ-shifted algorithmic (ε, C)-scatter dimension λ(·); reason: the class's C_M restricted to each metric is such an oracle, so the paper's hypothesis implies this one; every call costs one step
--   - reading: d′^a ∈ R_+ in Definition 2.3 → d′^a > 0; reason: R_+ is the positive reals; fewer sequences are scatterings, so the scatter-dimension hypothesis is weaker and the theorem stronger
--   - encoding: λ: R≥0 → N → lam : ℝ → ℕ (values on negative reals unused); reason: Lean convention; every λ on R≥0 extends
--   - encoding: OPT_I, the value of 'the optimal solution' → the infimum of f(U(X, σ)) over X ∈ F^k and σ (nonempty, bounded below by 0); reason: with F infinite a minimum need not exist; equal to the minimum when it exists
--   - encoding: linear functions h_ℓ: R^k_{≥0} → R^d_{≥0} → nonnegative coefficients c_{ℓ,j,i} with (h_ℓ z)_j = Σ_i c_{ℓ,j,i} z_i, given as input reals; reason: every such linear map has this form (p. 79 obtains the coefficients by evaluating h_ℓ on unit vectors)
--   - encoding: index sets [k], [d], [ψ], [n] (1-based) → Fin k, Fin d, Fin ψ, Fin n (0-based); P an injective family Fin n → α; reason: Lean convention; same instances
--   - encoding: row-wise ordered norm f → RowInstance: the instance carries (W, f′) with f = rowOrdNorm W f′; the weights are input reals and f′ an oracle; reason: §4 (p. 46) describes f through W and f′; same objectives
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 8, Theorem 1.5

import Mathlib
import Definitions.Def_DistMapClust_Main_IO

open MeasureTheory

namespace DistMapClust.Main

/-- Theorem 1.5 (p. 8). For every `λ`, every `χ ∈ [0, 2]`, every class constant `c` of §A.1(3) and
every class of instances with row-wise ordered norm objectives whose metric spaces, with their Ball
Intersection oracles, have `χ`-shifted algorithmic `ε`-scatter dimension `λ(·)`, there are one
program, a function `ζ` and constants `C, e` such that on every instance of the class, every size
parameter `s ≥ n, k, d, ψ` with `2^{-s^c} ≤ OPT_I ≤ 2^{s^c}` and every `ε ∈ (0, 1/48)`: every run on
`(I, χ, ε)` halts within `ζ(k, d, ψ, 1/ε, λ(ε/100)) · (C s^e + C)` steps and outputs `X ∈ F^k` and
`σ : P → [ψ]`, and the probability that `f(U(X, σ)) > (1 + χ + ε) OPT_I` is at most `1/n`. -/
theorem theorem_1_5 :
    ∀ (lam : ℝ → ℕ) (χ : ℝ), 0 ≤ χ → χ ≤ 2 → ∀ (c : ℕ) (α : Type) (Cls : Set (RowInstance α)),
      (∀ I ∈ Cls, HasScatterDim (Set.range I.P) I.F I.δ I.C χ lam) →
      ∃ prog : Program, Admissible prog ∧
        ∃ (ζ : ℕ → ℕ → ℕ → ℝ → ℕ → ℝ) (C e : ℕ),
          ∀ I ∈ Cls, ∀ s : ℕ, I.n ≤ s → I.k ≤ s → I.d ≤ s → I.ψ ≤ s → OptBounded s c I.OPT →
          ∀ ε : ℝ, 0 < ε → ε < 1 / 48 →
            (∀ ν : Tape, HaltsWithin prog (I.oracles fun x => (lam x : ℝ)) ν
              (I.start s ([χ, ε] ++ I.coefList ++ I.weightList))
              (ζ I.k I.d I.ψ (1 / ε) (lam (ε / 100)) * ((C : ℝ) * (s : ℝ) ^ e + C))) ∧
            (∀ (ν : Tape) (S : State α), finalState prog (I.oracles fun x => (lam x : ℝ)) ν
              (I.start s ([χ, ε] ++ I.coefList ++ I.weightList)) = some S →
                (∀ i, outCenters S I.k i ∈ I.F) ∧ ValidSel S I.n I.ψ) ∧
            tapeLaw {ν : Tape | ¬ ∃ S : State α,
                finalState prog (I.oracles fun x => (lam x : ℝ)) ν
                  (I.start s ([χ, ε] ++ I.coefList ++ I.weightList)) = some S ∧
                I.cost (outCenters S I.k) (outSel S I.n I.ψ I.ψ_pos) ≤ (1 + χ + ε) * I.OPT}
              ≤ ENNReal.ofReal (1 / (I.n : ℝ)) := by sorry

end DistMapClust.Main
