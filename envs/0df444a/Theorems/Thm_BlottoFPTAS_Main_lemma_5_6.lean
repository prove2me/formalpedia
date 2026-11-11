-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_lemma_5_6
-- name    : BlottoFPTAS.Main.lemma_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:43:34.145604+00:00
-- url     : https://prove2.me/theorems/217578a1-2c14-40b4-b422-6c9cb422976d
-- title:
--   Lemma 5.6 — deterministic computation of T candidate allocations per budget with U(P_A; ρ) ≤ C₁ + 3z/64 and U(P_B; 1) ≤ C_ρ + 3z/64, in both cost models
-- statement:
--   There are universal constants $C_0,k_0$ and, in each cost model, a deterministic program such that, for every reduced game of §5 ($2\le m<18/e$, $e=2^{-a}$, $a\ge1$, values $\hat v_j=\hat w_j/Q_v$ with integers $\hat w_j\ge1$ and $Q_v=\sum_j\hat w_j<512m/e+m$) and every rational $\rho\in(0,1)$ with denominator at most $q$: for each budget $c\in\{1,\rho\}$ the program computes a list of $T$ candidate allocations (elements of $X=\{x\in S^m:\sum_jx_j\le c\}$, $S$ the candidate bids of App. C.3), and with $P_A$, $P_B$ the uniform distributions on the lists for $c=1$ and $c=\rho$ (counting repeats),
--   $$U_{\hat v}(P_A;\rho)\le C_1+\tfrac{3z}{64},\qquad U_{\hat v}(P_B;1)\le C_\rho+\tfrac{3z}{64},\qquad U_{\hat v}(P_A;\rho)+U_{\hat v}(P_B;1)\le1+\tfrac{3z}{32}.\tag{13}$$
--   The two runs together use at most $C_0(m\Lambda^2/z^2+m\Lambda/z^4)\,\mathrm{polylog}+C_0$ real-RAM operations, respectively $C_0(m\Lambda^3/z^2+m\Lambda^2/z^4)\,\mathrm{polylog}+C_0$ bit operations, and each uses at most $C_0(m\Lambda^2/z^2)\,\mathrm{polylog}+C_0$ working bits, where $\mathrm{polylog}=\log_2(2+m+\Lambda+1/z)^{k_0}$ and $T,\Lambda,z,q$ are the parameters of Appendix C.2. This is the multiplicative-weights core of the approximation scheme.
--
--   Differences from the source:
--   - reading: the algorithm below computes … The computation is deterministic and uses Õ(·) operations → there exist a deterministic real-RAM program and a deterministic finite-bit program with these outputs and bounds; reason: the Appendix D implementation is not formalized; existence of a program is the content of the cost claim
--   - reading: Õ(mΛ²/z² + mΛ/z⁴), Õ(mΛ³/z² + mΛ²/z⁴), Õ(mΛ²/z²) → C₀ · f · log₂(2 + m + Λ + 1/z)^k₀ + C₀ with C₀, k₀ universal; operation and bit counts for the two budgets together, working bits for each; reason: standard reading of Õ; Lemma 5.7 Part 3 states the bounds for both budgets together
--   - reading: the reduced game of §5 (m battlefields, values v̂ with common denominator Q_v) → hypotheses 2 ≤ m < 18/e and Q_v = ∑ŵ_j < 512m/e + m, input given as the integer weights ŵ; reason: the standing assumptions of §5.1–5.2 (pp. 31, 55) under which the lemma is stated
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 35, Lemma 5.6

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game
import Definitions.Def_BlottoFPTAS_Main_Params
import Definitions.Def_BlottoFPTAS_Main_LearnIO

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **Lemma 5.6** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 35).
There are universal constants `C₀, k₀` and, in each cost model, a deterministic program such
that for every reduced game of §5 (`2 ≤ m < 18/e`, `e = 2^{-a}`, `a ≥ 1`, values `v̂_j = ŵ_j/Q_v`
with integers `ŵ_j ≥ 1` and `Q_v = ∑_j ŵ_j < 512m/e + m`) and every rational `ρ ∈ (0, 1)` with
denominator at most `q`: for each budget `c ∈ {1, ρ}` the program computes a list of `T`
candidate allocations (allocations in `X = {x ∈ S^m : ∑_j x_j ≤ c}`, `S` the candidate bids of
App. C.3); with `P_A`, `P_B` the uniform distributions on the lists for `c = 1` and `c = ρ`,
`U_v̂(P_A; ρ) ≤ C₁ + 3z/64`, `U_v̂(P_B; 1) ≤ C_ρ + 3z/64` and
`U_v̂(P_A; ρ) + U_v̂(P_B; 1) ≤ 1 + 3z/32` (13). The two runs together use at most
`C₀ (mΛ²/z² + mΛ/z⁴) polylog + C₀` real-RAM operations, resp. `C₀ (mΛ³/z² + mΛ²/z⁴) polylog + C₀`
bit operations, and each uses at most `C₀ (mΛ²/z²) polylog + C₀` working bits, with
`polylog = log₂(2 + m + Λ + 1/z)^{k₀}`. `T`, `Λ`, `z`, `q` are the parameters of Appendix C.2. -/
theorem lemma_5_6 :
    ∃ C₀ k₀ : ℕ,
      (∃ prog : RealRAM.Program, RealRAM.Admissible prog ∧ RealRAM.Deterministic prog ∧
        ∀ (m a : ℕ) (wh : Fin m → ℕ) (ρ : ℚ), 2 ≤ m → 1 ≤ a → (m : ℝ) < 18 / eR a →
          (∀ j, 1 ≤ wh j) → ((∑ j, wh j : ℕ) : ℝ) < 512 * m / eR a + m →
          0 < ρ → ρ < 1 → ρ.den ≤ qDen m a →
          let vh : Fin m → ℝ := fun j => (wh j : ℝ) / (∑ i, wh i : ℕ)
          let T := Titer m a
          let polylog : ℝ := Real.logb 2 (2 + m + Lam m a + 1 / zR a) ^ k₀
          ∃ outA outB : List ℝ,
            RealRAM.output prog (learnRealInput m a wh ρ false) RealRAM.zeroTape = some outA ∧
            RealRAM.output prog (learnRealInput m a wh ρ true) RealRAM.zeroTape = some outB ∧
            outA.length = T * m ∧ outB.length = T * m ∧
            (∀ x ∈ realAllocs m T outA, x ∈ candAllocs m a 1) ∧
            (∀ x ∈ realAllocs m T outB, x ∈ candAllocs m a ρ) ∧
            U vh (uniformList (realAllocs m T outA)) ρ ≤ minSup m vh 1 ρ + 3 * zR a / 64 ∧
            U vh (uniformList (realAllocs m T outB)) 1 ≤ minSup m vh ρ 1 + 3 * zR a / 64 ∧
            U vh (uniformList (realAllocs m T outA)) ρ +
                U vh (uniformList (realAllocs m T outB)) 1 ≤ 1 + 3 * zR a / 32 ∧
            ∃ kA kB : ℕ,
              (RealRAM.run prog (learnRealInput m a wh ρ false) RealRAM.zeroTape kA).halted
                = true ∧
              (RealRAM.run prog (learnRealInput m a wh ρ true) RealRAM.zeroTape kB).halted
                = true ∧
              ((kA + kB : ℕ) : ℝ) ≤
                C₀ * (m * Lam m a ^ 2 / zR a ^ 2 + m * Lam m a / zR a ^ 4) * polylog + C₀) ∧
      (∃ prog : BitRAM.Program, BitRAM.Deterministic prog ∧
        ∀ (m a : ℕ) (wh : Fin m → ℕ) (ρ : ℚ), 2 ≤ m → 1 ≤ a → (m : ℝ) < 18 / eR a →
          (∀ j, 1 ≤ wh j) → ((∑ j, wh j : ℕ) : ℝ) < 512 * m / eR a + m →
          0 < ρ → ρ < 1 → ρ.den ≤ qDen m a →
          let vh : Fin m → ℝ := fun j => (wh j : ℝ) / (∑ i, wh i : ℕ)
          let T := Titer m a
          let polylog : ℝ := Real.logb 2 (2 + m + Lam m a + 1 / zR a) ^ k₀
          let inA := learnBitInput m a wh ρ false
          let inB := learnBitInput m a wh ρ true
          BitRAM.Halts prog inA BitRAM.zeroTape ∧ BitRAM.Halts prog inB BitRAM.zeroTape ∧
          ∃ LA LB : List (Fin m → ℝ),
            bitAllocs m T (BitRAM.output prog inA BitRAM.zeroTape) = some LA ∧
            bitAllocs m T (BitRAM.output prog inB BitRAM.zeroTape) = some LB ∧
            (∀ x ∈ LA, x ∈ candAllocs m a 1) ∧ (∀ x ∈ LB, x ∈ candAllocs m a ρ) ∧
            U vh (uniformList LA) ρ ≤ minSup m vh 1 ρ + 3 * zR a / 64 ∧
            U vh (uniformList LB) 1 ≤ minSup m vh ρ 1 + 3 * zR a / 64 ∧
            U vh (uniformList LA) ρ + U vh (uniformList LB) 1 ≤ 1 + 3 * zR a / 32 ∧
            (((BitRAM.bitCost prog inA BitRAM.zeroTape + BitRAM.bitCost prog inB BitRAM.zeroTape :
                ℕ) : ℝ) ≤
              C₀ * (m * Lam m a ^ 3 / zR a ^ 2 + m * Lam m a ^ 2 / zR a ^ 4) * polylog + C₀) ∧
            (((max (BitRAM.workingBits prog inA BitRAM.zeroTape)
                (BitRAM.workingBits prog inB BitRAM.zeroTape) : ℕ) : ℝ) ≤
              C₀ * (m * Lam m a ^ 2 / zR a ^ 2) * polylog + C₀)) := by sorry

end BlottoFPTAS.Main
