-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_prop1_base_code
-- name    : ExpanderWalkDecode.Main.prop1_base_code
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:59.208225+00:00
-- url     : https://prove2.me/theorems/72aee5d4-1d1c-4491-ae2b-2b9230fd3416
-- title:
--   Proposition 1 — explicit base codes of bias $\varepsilon_{\mathrm{base}}$, rate $\Omega(\varepsilon_{\mathrm{base}}^C)$, list decodable at $2\sqrt{\varepsilon_{\mathrm{base}}}$ in near-linear time
-- statement:
--   There are absolute constants $C>0$, $\kappa>0$, $K$, $p$, $c$ and $c_0>0$ such that for every $\varepsilon_{\mathrm{base}}>0$ there is a family of binary linear codes $C_{n,\mathrm{base}}\subseteq\mathbb F_2^n$, one of every blocklength $n$, with:
--
--   1. bias at most $\varepsilon_{\mathrm{base}}$ for every $n$;
--   2. rate at least $\kappa\min(\varepsilon_{\mathrm{base}},1)^C$ for all $n\ge n_0(\varepsilon_{\mathrm{base}})$;
--   3. explicitness: one program outputs a generator matrix of $C_{n,\mathrm{base}}$ in time polynomial in $n$;
--   4. list decoding: one program that, for every $n\ge1$ and every $\rho_{\mathrm{base}}\ge2\sqrt{\varepsilon_{\mathrm{base}}}$, outputs $\mathrm{LIST}(Y,\rho_{\mathrm{base}})$ with probability at least $c_0$ within
--   $$K\,n\,(\log_2(n+2))^p\,(1+1/\varepsilon_{\mathrm{base}})^{c}=\tilde O(n)\cdot\mathrm{poly}(1/\varepsilon_{\mathrm{base}})$$
--   steps on every received word $Y$.
--
--   These are the base codes on which the walk construction is applied.
--
--   Differences from the source:
--   - reading: an explicit family {C_{k,base}}_{k∈ℕ}, decoding in time Õ(k) → one code of every blocklength n, decoding time in n, the rate bound for n ≥ n₀(ε_base); reason: §4 uses a base code of the free length n; an asymptotic rate is an eventual bound
--   - reading: explicit → one program outputs a generator matrix in time Kg (n+1)^Kg; reason: explicit = constructible in polynomial time
--   - reading: ρ_base-list-decodable (Definition 1: constant success probability) → one program for all n and ρ_base, success probability ≥ c₀ for an absolute c₀ > 0, worst-case time on the machine of this mission; reason: Definition 1 with a uniform algorithm; a per-code algorithm could be a lookup table
--   - reading: bias at most ε_base → every nonzero codeword has |sign average| ≤ ε_base; reason: the paper's small-bias convention (absolute bias)
--   - encoding: rate Ω(ε_base^C), time Õ(k)·poly(1/ε_base) → κ·min(ε_base,1)^C and K n (log₂(n+2))^p (1+1/ε_base)^c with absolute constants; reason: unfolding of the asymptotic notation; min and 1+1/ε only change constants for ε_base ≥ 1/2
--   - reading: algorithmic running time, without an explicit machine specification → the mission machine: a unit-cost real RAM with √, natural logarithm, fair coins and an exact symmetric eigendecomposition charged d³+1; reason: the source thresholds eigenvalues exactly (Figure 3), takes exact top eigenvectors (Figure 4) and sets parameters by logarithmic formulas (Δ, ℓ), counting these steps as polynomial work; an exact eigenvalue threshold is meaningful only in exact real arithmetic, so this is the model the source computes in; the cubic charge is one polynomial cost for the step the source calls immediate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 8 (PDF p. 11), §3.1, Proposition 1

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Codes

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Proposition 1 (The Base Code) (§3.1, p. 8): there are absolute constants `C > 0` (rate
exponent), `κ > 0`, `K`, `p`, `c` and `c₀ > 0` such that for every `ε_base > 0` there is an explicit
family of binary linear codes, one of each blocklength `n`, with bias at most `ε_base`, rate at least
`κ min(ε_base, 1)^C` for all large `n`, and a list decoder that, for every `ρ_base ≥ 2√ε_base`,
outputs `LIST(Y, ρ_base)` with probability at least `c₀` within `K n (log₂(n+2))^p (1+1/ε_base)^c`
steps; a second program outputs a generator matrix of the code of blocklength `n` in time polynomial
in `n`. -/
theorem prop1_base_code :
    ∃ (C κ K c c₀ : ℝ) (p : ℕ), 0 < C ∧ 0 < κ ∧ 0 < c₀ ∧
      ∀ εb : ℝ, 0 < εb →
        ∃ (Cb : ∀ n : ℕ, BinaryLinearCode n) (Pgen Pdec : Program) (Kg : ℝ) (n₀ : ℕ),
          Admissible Pgen ∧ Admissible Pdec ∧
          (∀ n : ℕ, HasBias (Cb n) εb) ∧
          (∀ n : ℕ, n₀ ≤ n → κ * (min εb 1) ^ C ≤ rate (Cb n)) ∧
          (∀ n : ℕ, RunsWithin Pgen (natInput n) (Kg * ((n : ℝ) + 1) ^ Kg)
            (fun out => EncodesGenerator out (Cb n)) 1) ∧
          ∀ n : ℕ, 1 ≤ n → ∀ ρb : ℝ, 2 * Real.sqrt εb ≤ ρb →
            ListDecodesWithin Pdec Cb ρb n
              (K * n * Real.logb 2 ((n : ℝ) + 2) ^ p * (1 + 1 / εb) ^ c) c₀ := by sorry

end ExpanderWalkDecode.Main
