-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim12_soft_base_decoder
-- name    : ExpanderWalkDecode.Main.claim12_soft_base_decoder
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:24:40.167167+00:00
-- url     : https://prove2.me/theorems/8e28b3bf-f515-4986-bca6-f014fed8208c
-- title:
--   Claim 12 — soft-input base list decoder, both printed output contracts
-- statement:
--   Let $0<\lambda\le1/4$ and let $\{C_{n,\mathrm{base}}\}$ be a family of binary linear codes with bias at most $\lambda^2/4$ that has a list decoder as in Proposition 1 at $\varepsilon_{\mathrm{base}}=\lambda^2/4$ (one program, every radius $\rho_{\mathrm{base}}\ge2\sqrt{\lambda^2/4}=\lambda$, success probability $c_0>0$, time $K_dn(\log_2(n+2))^{p_d}(1+4/\lambda^2)^{c_d}$). There are positive constants $K,c$ and a power $p$, depending only on the base-decoder bounds $K_d,c_d,c_0,p_d$, chosen before $\lambda$, the family and its decoding program. For each such $\lambda$ and decoder there are programs $D_n$, $D_A$ such that for all $n\ge1$, every embedding $\iota:[n]\hookrightarrow A$, every $\delta>0$ and every soft word $Z'\in[-1,1]^A$, both run within $Kn(\log_2(n+2))^p\lambda^{-c}\log(2+1/\delta)=\tilde O(n)\cdot\mathrm{poly}(1/\lambda)\cdot\log(1/\delta)$ steps, and with probability at least $1-\delta$:
--
--   1. (Claim 12 (Restated), Appendix C.2) $D_n$ outputs $\{Z\in C_{n,\mathrm{base}}:\mathbb E_{i\sim[n]}[Z_iZ'_{\iota(i)}]\ge2\lambda\}$;
--   2. (Claim 12, §4.3) if $|A|\le(1+\lambda^2)n$, $D_A$ outputs $\{Z\in C_{n,\mathrm{base}}:\mathbb E_{a\sim A}[Z_aZ'_a]\ge2\lambda\}$, $Z$ padded by $+1$ off $\iota([n])$.
--
--   The rounding step calls this decoder on the soft words it constructs.
--
--   Differences from the source:
--   - generalization: the family of base codes used in the construction (Proposition 1 at ε_base = λ²/4) → any family with bias ≤ λ²/4 and a Proposition-1 list decoder at every radius ≥ λ; reason: these are the properties of the Proposition 1 family that the claim uses; specializes
--   - reading: two printed output sets: E_a[Z_a Z′_a] ≥ 2λ (p. 16) and E_i[Z_i Z′_{ι(i)}] ≥ 2λ (p. 28) → both, by two programs; the padded-A form under |A| ≤ (1+λ²)n; reason: the two sets differ when |A| > n; the construction has |A| = n(1+o_n(1)); without a size bound the padded list can contain the whole code
--   - reading: time Õ(k)·poly(1/λ)·log(1/δ) for every k → K n (log₂(n+2))^p λ^{-c} log(2+1/δ) for every n ≥ 1; reason: unfolding of the asymptotic notation; log(2+1/δ) is defined for every δ > 0
--   - encoding: Õ(n) poly(1/λ) with constants controlled by the base decoder → K,c,p chosen before λ, C_base and P_dec; programs after them; reason: the constants must be uniform in λ. The previous quantifier order allowed arbitrary dependence on λ
--   - reading: algorithmic running time, without an explicit machine specification → the mission machine: a unit-cost real RAM with √, natural logarithm, fair coins and an exact symmetric eigendecomposition charged d³+1; reason: the source thresholds eigenvalues exactly (Figure 3), takes exact top eigenvectors (Figure 4) and sets parameters by logarithmic formulas (Δ, ℓ), counting these steps as polynomial work; an exact eigenvalue threshold is meaningful only in exact real arithmetic, so this is the model the source computes in; the cubic charge is one polynomial cost for the step the source calls immediate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 16 (PDF p. 19), §4.3, Claim 12; Claim 12 (Restated), p. 28 (PDF p. 31)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Encoding

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 12 (Soft Base List-Decoder) (§4.3, p. 16; Claim 12 (Restated), Appendix C.2, p. 28):
for a family of base codes with bias at most `λ²/4` and a list decoder at every radius
`ρ_base ≥ λ = 2√(λ²/4)` as in Proposition 1, and every `δ > 0`, there are randomized programs running
in time `Õ(n) poly(1/λ) log(1/δ)` that on input `Z′ ∈ [-1, 1]^A` output, with probability at least
`1 - δ`: (restated form) `{Z ∈ C_base : E_i[Z_i Z′_{ι(i)}] ≥ 2λ}`; (form of §4.3) for the padded
embedding with `|A| ≤ (1 + λ²) n`, `{Z ∈ C_base : E_a[Z_a Z′_a] ≥ 2λ}`. -/
theorem claim12_soft_base_decoder :
    ∀ (Kd cd c₀ : ℝ) (pd : ℕ), 0 < c₀ →
      ∃ (K c : ℝ) (p : ℕ), 0 < K ∧ 0 < c ∧
      ∀ (lam : ℝ) (Cb : ∀ n : ℕ, BinaryLinearCode n) (Pdec : Program),
      0 < lam → lam ≤ 1 / 4 → Admissible Pdec →
      (∀ n : ℕ, HasBias (Cb n) (lam ^ 2 / 4)) →
      (∀ n : ℕ, 1 ≤ n → ∀ ρb : ℝ, 2 * Real.sqrt (lam ^ 2 / 4) ≤ ρb →
        ListDecodesWithin Pdec Cb ρb n
          (Kd * n * Real.logb 2 ((n : ℝ) + 2) ^ pd * (1 + 1 / (lam ^ 2 / 4)) ^ cd) c₀) →
      ∃ (PA Pn : Program), Admissible PA ∧ Admissible Pn ∧
        ∀ (n nA : ℕ) (ι : Fin n ↪ Fin nA) (δ : ℝ) (Z' : Fin nA → ℝ),
          1 ≤ n → 0 < δ → (∀ a, Z' a ∈ Set.Icc (-1 : ℝ) 1) →
          RunsWithin Pn (softInput ι δ lam Z')
            (K * n * Real.logb 2 ((n : ℝ) + 2) ^ p * (1 / lam) ^ c * Real.log (2 + 1 / δ))
            (fun out => EncodesWordList out (softListN (Cb n) ι lam Z')) (1 - δ) ∧
          ((nA : ℝ) ≤ (1 + lam ^ 2) * n →
            RunsWithin PA (softInput ι δ lam Z')
              (K * n * Real.logb 2 ((n : ℝ) + 2) ^ p * (1 / lam) ^ c * Real.log (2 + 1 / δ))
              (fun out => EncodesWordList out (softListA (Cb n) ι lam Z')) (1 - δ)) := by sorry

end ExpanderWalkDecode.Main
