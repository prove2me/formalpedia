-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_theorem_5_1
-- name    : BlottoFPTAS.Main.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:43:13.750989+00:00
-- url     : https://prove2.me/theorems/753e9c1f-34f7-4686-95dd-9ea08a19e66b
-- title:
--   Theorem 5.1 — an FPTAS for ε-Nash equilibria of continuous Colonel Blotto with common values, in the real-RAM and finite-bit models
-- statement:
--   There are universal constants $C,k\in\mathbb N$ and, in each of two cost models — (i) the unit-cost randomized real RAM, (ii) the finite-bit (log-cost rational) RAM with fair coins — a deterministic construction program and a sampler program such that, for every game with $n\ge1$ battlefields, rational values $v_i>0$ with $\sum_iv_i=1$, rational $b\in(0,1]$, and every rational $0<\varepsilon<1$: the construction halts on each player's input and outputs a finite description; the laws $\mu_A,\mu_B$ of the sampler run on the two descriptions form an $\varepsilon$-Nash equilibrium of the continuous game (regrets are suprema over all of $X(c)\subseteq\mathbb R^n$); and every sampled allocation lies in the player's $X(c)$. Moreover, with $n_*=\min\{n,1/\varepsilon\}$, $L_0$, $E$ the binary lengths of $(v,b)$ and $\varepsilon$, and $\mathrm{polylog}=\log_2(2+L_0+E+n+\lceil1/\varepsilon\rceil)^k$:
--   - real-RAM construction (both runs): at most $C(n+n_*^2/\varepsilon^5)\log_2(2+n+\lceil1/\varepsilon\rceil)^k+C$ operations;
--   - finite-bit construction: at most $C(L_0+E+n_*^3/\varepsilon^6)\,\mathrm{polylog}+C$ bit operations and $C(L_0+E+n_*^3/\varepsilon^4)\,\mathrm{polylog}+C$ working bits; the two descriptions together have at most $C(L_0+E+n+n_*^2/\varepsilon^3)\,\mathrm{polylog}+C$ bits;
--   - every real-RAM draw halts within $C(n+\log_2(1/\varepsilon))+C$ operations and outputs $n$ coordinates;
--   - if $n>1$ and $b<1$, every finite-bit draw halts with at most $C\log_2(n/\varepsilon)+C$ random bits and $Cn(L_0+n_*/\varepsilon)\,\mathrm{polylog}+C$ bit operations, writing the $n$ rational coordinates included;
--   - if $n>1$ and $b=1$, the finite-bit sampler halts almost surely and the same two bounds hold in expectation;
--   - if $n=1$, $\mu_A=\delta_{(1)}$, $\mu_B=\delta_{(b)}$ and the pair is an exact Nash equilibrium.
--
--   This is the first FPTAS for continuous Colonel Blotto with arbitrary common values and budgets.
--
--   **Formalization Note.** Strategies are the pushforwards of the tape measure (product of $\mathrm{Unif}[0,1]$, resp. of fair coins) under the sampler's output; the sampler reads only its description. Feasibility is required on every tape (real RAM: every tape with cells in $[0,1]$; finite-bit: every halting tape).
--
--   Differences from the source:
--   - reading: a deterministic algorithm computes … In the real-RAM model … in the finite-bit model … → one construction program and one sampler program per model, each with the full ε-Nash guarantee and that model's bounds; reason: the paper analyses one algorithm in both models; each model needs its own program
--   - reading: Õ(f) and O(f) → C·f·log₂(2 + N)^k + C and C·f + C with C, k ∈ ℕ universal, N = n + ⌈1/ε⌉ for the real-RAM construction and N = L0 + E + n + ⌈1/ε⌉ for finite-bit quantities; reason: standard reading with constants fixed before the instance; App. F.4–F.5 show no L0 dependence of the real-RAM count
--   - encoding: a deterministic algorithm computes finite descriptions of the two strategies → the construction program runs once per player (player flag as last input) and outputs that player's description; the bounds cover both runs; reason: equivalent up to a factor 2 to one run producing both
--   - encoding: real-RAM model; finite-bit model with Rat(W) = Õ(W) → the RealRAM machine (rational literals, indexed storage, Unif[0, 1] tape) and the BitRAM log-cost rational RAM with Rat(W) = W + 1, random access to the input bits (inBitAt, charged by the address length), fair-coin tape and working bits including the output; reason: the paper's models made concrete; Rat(W) = W + 1 gives the same Õ bounds; random access lets a sampler read one row of its stored description, as the per-draw costs of App. F.6 assume
--   - encoding: strategies forming an ε-Nash equilibrium; every sampled allocation satisfies the budget → the laws of the sampler on the descriptions (pushforward of the tape measure) satisfy IsEpsNash; feasibility on every supported (real) or halting (bit) tape; reason: Lean convention for the output distribution of a randomized program
--   - encoding: rational game input, battlefields [n] → Instance with ℚ data cast to ℝ, battlefields Fin n; reason: Lean convention
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), pp. 27–28, Theorem 5.1

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Inputs

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **Theorem 5.1** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…,
pp. 27–28). There are universal constants `C, k` and, in each of the two cost models, a
deterministic construction program and a sampler program such that, for every instance
`(n, v, b)` with rational data and every rational `0 < ε < 1`, the laws of the sampler run on the
two computed descriptions form an `ε`-Nash equilibrium of the continuous game, every sampled
allocation is feasible, and the stated construction, storage, description and sampling bounds
hold; for `n = 1` the strategies are the full-budget point masses and form an exact
equilibrium. `Õ(f)` is read as `C · f · log₂(2 + N)^k + C` with `N = n + ⌈1/ε⌉` for the real-RAM
construction and `N = L0 + E + n + ⌈1/ε⌉` for finite-bit quantities; `O(f)` is `C · f + C`. -/
theorem theorem_5_1 :
    ∃ C k : ℕ,
      -- (i) the real-RAM implementation
      (∃ cons samp : RealRAM.Program,
        RealRAM.Admissible cons ∧ RealRAM.Deterministic cons ∧ RealRAM.Admissible samp ∧
        ∀ (I : Instance) (ε : ℚ), 0 < ε → ε < 1 →
          ∃ dA dB : List ℝ,
            RealRAM.output cons (realInput I ε false) RealRAM.zeroTape = some dA ∧
            RealRAM.output cons (realInput I ε true) RealRAM.zeroTape = some dB ∧
            (∃ kA kB : ℕ,
              (RealRAM.run cons (realInput I ε false) RealRAM.zeroTape kA).halted = true ∧
              (RealRAM.run cons (realInput I ε true) RealRAM.zeroTape kB).halted = true ∧
              ((kA + kB : ℕ) : ℝ) ≤
                C * ((I.n : ℝ) + nStar I.n ε ^ 2 / (ε : ℝ) ^ 5) *
                  Real.logb 2 (2 + I.n + ⌈(1 / (ε : ℝ))⌉₊) ^ k + C) ∧
            IsEpsNash I.vR I.b ε (RealRAM.law samp dA I.n) (RealRAM.law samp dB I.n) ∧
            (∀ ω : ℕ → ℝ, RealRAM.TapeInSupport ω →
              RealRAM.HaltsWithin samp dA ω (C * ((I.n : ℝ) + Real.logb 2 (1 / (ε : ℝ))) + C) ∧
              (∃ out : List ℝ, RealRAM.output samp dA ω = some out ∧ out.length = I.n ∧
                RealRAM.toAlloc I.n (some out) ∈ X I.n 1)) ∧
            (∀ ω : ℕ → ℝ, RealRAM.TapeInSupport ω →
              RealRAM.HaltsWithin samp dB ω (C * ((I.n : ℝ) + Real.logb 2 (1 / (ε : ℝ))) + C) ∧
              (∃ out : List ℝ, RealRAM.output samp dB ω = some out ∧ out.length = I.n ∧
                RealRAM.toAlloc I.n (some out) ∈ X I.n I.b)) ∧
            (I.n = 1 →
              RealRAM.law samp dA I.n = Measure.dirac (fun _ => (1 : ℝ)) ∧
              RealRAM.law samp dB I.n = Measure.dirac (fun _ => (I.b : ℝ)) ∧
              IsEpsNash I.vR I.b 0 (RealRAM.law samp dA I.n) (RealRAM.law samp dB I.n))) ∧
      -- (ii) the finite-bit implementation
      (∃ cons samp : BitRAM.Program,
        BitRAM.Deterministic cons ∧
        ∀ (I : Instance) (ε : ℚ), 0 < ε → ε < 1 →
          let inA := bitInput I ε false
          let inB := bitInput I ε true
          let dA := BitRAM.output cons inA BitRAM.zeroTape
          let dB := BitRAM.output cons inB BitRAM.zeroTape
          let polylog : ℝ :=
            Real.logb 2 (2 + L0 I + Elen ε + I.n + ⌈(1 / (ε : ℝ))⌉₊) ^ k
          BitRAM.Halts cons inA BitRAM.zeroTape ∧ BitRAM.Halts cons inB BitRAM.zeroTape ∧
          (((BitRAM.bitCost cons inA BitRAM.zeroTape + BitRAM.bitCost cons inB BitRAM.zeroTape :
              ℕ) : ℝ) ≤
            C * ((L0 I : ℝ) + Elen ε + nStar I.n ε ^ 3 / (ε : ℝ) ^ 6) * polylog + C) ∧
          (((max (BitRAM.workingBits cons inA BitRAM.zeroTape)
              (BitRAM.workingBits cons inB BitRAM.zeroTape) : ℕ) : ℝ) ≤
            C * ((L0 I : ℝ) + Elen ε + nStar I.n ε ^ 3 / (ε : ℝ) ^ 4) * polylog + C) ∧
          (((dA.length + dB.length : ℕ) : ℝ) ≤
            C * ((L0 I : ℝ) + Elen ε + I.n + nStar I.n ε ^ 2 / (ε : ℝ) ^ 3) * polylog + C) ∧
          IsEpsNash I.vR I.b ε (BitRAM.law samp dA I.n) (BitRAM.law samp dB I.n) ∧
          (∀ ω : ℕ → Bool, BitRAM.Halts samp dA ω →
            ∃ x : Fin I.n → ℚ, BitRAM.decodeAlloc I.n (BitRAM.output samp dA ω) = some x ∧
              (fun i => (x i : ℝ)) ∈ X I.n 1) ∧
          (∀ ω : ℕ → Bool, BitRAM.Halts samp dB ω →
            ∃ y : Fin I.n → ℚ, BitRAM.decodeAlloc I.n (BitRAM.output samp dB ω) = some y ∧
              (fun i => (y i : ℝ)) ∈ X I.n I.b) ∧
          (1 < I.n → I.b < 1 →
            ∀ d ∈ [dA, dB], ∀ ω : ℕ → Bool,
              BitRAM.Halts samp d ω ∧
              (BitRAM.randomBits samp d ω : ℝ) ≤ C * Real.logb 2 (I.n / (ε : ℝ)) + C ∧
              (BitRAM.bitCost samp d ω : ℝ) ≤
                C * I.n * ((L0 I : ℝ) + nStar I.n ε / ε) * polylog + C) ∧
          (1 < I.n → I.b = 1 →
            ∀ d ∈ [dA, dB],
              (∀ᵐ ω ∂BitRAM.coinTape, BitRAM.Halts samp d ω) ∧
              ∫⁻ ω, BitRAM.randomBitsE samp d ω ∂BitRAM.coinTape ≤
                ENNReal.ofReal (C * Real.logb 2 (I.n / (ε : ℝ)) + C) ∧
              ∫⁻ ω, BitRAM.bitCostE samp d ω ∂BitRAM.coinTape ≤
                ENNReal.ofReal (C * I.n * ((L0 I : ℝ) + nStar I.n ε / ε) * polylog + C)) ∧
          (I.n = 1 →
            BitRAM.law samp dA I.n = Measure.dirac (fun _ => (1 : ℝ)) ∧
            BitRAM.law samp dB I.n = Measure.dirac (fun _ => (I.b : ℝ)) ∧
            IsEpsNash I.vR I.b 0 (BitRAM.law samp dA I.n) (BitRAM.law samp dB I.n))) := by sorry

end BlottoFPTAS.Main
