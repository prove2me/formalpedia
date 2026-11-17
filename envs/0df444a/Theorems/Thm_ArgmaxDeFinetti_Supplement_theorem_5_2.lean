-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_Supplement_theorem_5_2
-- name    : ArgmaxDeFinetti.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:45:32.472241+00:00
-- url     : https://prove2.me/theorems/ca8fcf93-d333-45f3-9e89-f4f5c0549118
-- title:
--   Theorem 5.2, p.38 — $h_{\mathrm{BEXT}_{n,n}}\le h_{\mathrm{SEP}}+\sqrt{\min\{d_A,d_B\}-1}/(2n)$; Best Separable State in subexponential time
-- statement:
--   For an operator $M$ on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ write $h_{\mathrm{SEP}}(M)=\max_{\sigma\in\mathrm{SEP}(d_A,d_B)}\mathrm{Tr}(M\sigma)$ and $h_{\mathrm{BEXT}_{n,n}}(M)=\max_{\rho\in\mathrm{BEXT}_{n,n}(d_A,d_B)}\mathrm{Tr}(M\rho)$.
--
--   1. Let $0\preceq M\preceq I$ and $n\ge1$. Then
--   $$
--   h_{\mathrm{SEP}}(M)\le h_{\mathrm{BEXT}_{n,n}}(M)\le h_{\mathrm{SEP}}(M)+\frac{\sqrt{\min\{d_A,d_B\}-1}}{2n}.
--   $$
--   2. There are absolute constants $C>0$, $k\in\mathbb N$ and one deterministic algorithm which, given $d$, a rational $\varepsilon\in(0,1]$ and an accepting operator $0\preceq M\preceq I$ on $\mathbb C^d\otimes\mathbb C^d$ with complex-rational entries, outputs a rational number within $\varepsilon$ of $h_{\mathrm{SEP}}(M)$ in at most
--   $$
--   (B+2)^k\exp\!\Big(C\frac{\sqrt d}{\varepsilon}\log\big(2+\varepsilon\sqrt d\big)\Big)
--   $$
--   steps, where $B$ is the bit length of the input.
--   3. With the same $C,k$ and an absolute $\kappa\in(0,1]$, one deterministic algorithm decides the promise problem $h_{\mathrm{SEP}}(M)\ge c$ versus $h_{\mathrm{SEP}}(M)\le s$ (for rationals $0\le s<c\le1$) within the same bound evaluated at $\varepsilon=\kappa(c-s)$.
--
--   Part 1 says the two-sided Bose-symmetric extension hierarchy approximates Best Separable State with an additive error independent of the value, removing the perfect-completeness assumption of earlier subexponential algorithms.
--
--   **Formalization Note** The algorithms are deterministic Turing machines with binary input and output; the input bit length includes $d$, $\varepsilon$ (resp. $c,s$) and every entry of $M$.
--
--   Differences from the source:
--   - reading: "can be approximated … deterministically" (no machine model named) → one fixed deterministic Turing machine (BitMachine: Mathlib FinTM2 with binary input and output) for all inputs; input d, then the rational parameters, then the matrix entries as complex rationals; output a rational in lowest terms, resp. one bit; reason: the paper fixes no model; Theorem 1.7 speaks of the input bit complexity, i.e. the bit model
--   - reading: "up to a factor polynomial in the bit complexity of M" (resp. ρ) → (B + 2)^k with B the length of the whole input encoding (d, the rational parameters and the matrix); reason: Theorems 1.7–1.8 say "input bit complexity"; reading the rational parameters costs their own length, so the factor cannot depend on the matrix alone
--   - reading: exp(O((√d/ε) log(2 + ε√d))) → exp(C·(√d/ε)·log(2 + ε√d)) with C > 0 and k absolute, chosen before d, ε and the input; reason: the implied constant is universal (standing assumption, Table 1 caption)
--   - reading: the promise problem is decidable "within the same bound with ε = Θ(c − s)" → a second fixed machine outputs true when h_SEP(M) ≥ c and false when h_SEP(M) ≤ s, within the bound at ε = κ(c − s) for an absolute κ ∈ (0, 1]; c, s rational inputs with 0 ≤ s < c ≤ 1; reason: Θ(c − s) names a constant multiple of c − s; nothing is required off the promise
--   - encoding: h_SEP(M) = max_{σ ∈ SEP} Tr(Mσ), h_BEXT(M) = max_{ρ ∈ BEXT} Tr(Mρ) → the base supportFn (sSup of the real part of Tr(Mρ)) of SEP(dA,dB), resp. BEXT_{n,n}(dA,dB); reason: the maxima over these compact sets are attained, so max = sup; Tr(Mρ) is real for Hermitian M
--   - encoding: explicitly given M on ℂ^d ⊗ ℂ^d; 0 ⪯ M ⪯ I → a matrix of complex rationals (real and imaginary parts in ℚ); M ⪰ 0 and I − M ⪰ 0; reason: Lean convention for explicit input
--   - encoding: ℂ^d (and ℂ^{dA}, ℂ^{dB}, n ≥ 1) → hypotheses 1 ≤ d (resp. 1 ≤ dA, 1 ≤ dB, 1 ≤ n); reason: excludes only empty spaces, where no state exists
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem 5.2, eqs. (5.9)–(5.10), p.38 (= Theorem 1.7, p.9); definitions (5.7)–(5.8), p.38

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_supportFn
import Definitions.Def_ArgmaxDeFinetti_Supplement_bext
import Definitions.Def_ArgmaxDeFinetti_Supplement_BitMachine

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

namespace Supplement

/-- **Theorem 5.2 (Subexponential BSS)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.38, eqs. (5.9)–(5.10) (= Theorem 1.7, p.9). Let `0 ⪯ M ⪯ I` act on
`H_A ⊗ H_B`. For every `n ≥ 1`, `h_SEP(M) ≤ h_{BEXT_{n,n}}(M) ≤ h_SEP(M) + √(min{dA, dB} − 1)/(2n)` (5.9).
Consequently, for an explicitly given accepting operator `M` on `ℂ^d ⊗ ℂ^d`, `h_SEP(M)` can be approximated to
additive error `ε ∈ (0, 1]` deterministically, in time polynomial in the bit complexity times
`exp(O((√d/ε) log(2 + ε√d)))` (5.10); the promise `h_SEP(M) ≥ c` versus `h_SEP(M) ≤ s` is decidable within the same
bound with `ε = Θ(c − s)`.

**Formalization Note**
* `h_SEP(M) = max_{σ ∈ SEP(dA,dB)} Tr(Mσ)` and `h_{BEXT_{n,n}}(M) = max_{ρ ∈ BEXT_{n,n}(dA,dB)} Tr(Mρ)` ((5.7)–(5.8)) are the
  base `supportFn` of the two sets; `0 ⪯ M ⪯ I` is `M ⪰ 0` and `I − M ⪰ 0`.
* Algorithms are `BitMachine`s (deterministic Turing machines, binary input and output), one fixed machine for all
  inputs. Input: `d`, then `ε` (resp. `c`, `s`), then the entries of `M` as complex rationals (`encMat`). Output: a
  rational within `ε` of `h_SEP(M)`, resp. one bit (`true` = "`h_SEP(M) ≥ c`").
* "Up to a factor polynomial in the bit complexity" is `(B + 2)^k` with `B` the length of the whole input (Theorem 1.7:
  "the input bit complexity"); `C`, `k` (and `κ`) are absolute, chosen before `d`, `ε` and the input.
* "`ε = Θ(c − s)`" is the bound evaluated at `ε = κ(c − s)` for an absolute `κ ∈ (0, 1]`; the promise inputs satisfy
  `0 ≤ s < c ≤ 1`. Nothing is required on inputs violating the hypotheses. -/
theorem theorem_5_2 :
    (∀ (dA dB n : ℕ) (M : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      1 ≤ dA → 1 ≤ dB → 1 ≤ n → M.PosSemidef → (1 - M).PosSemidef →
        supportFn (sepAB dA dB) M ≤ supportFn (bext n n dA dB) M ∧
        supportFn (bext n n dA dB) M ≤
          supportFn (sepAB dA dB) M + Real.sqrt (((min dA dB : ℕ) : ℝ) - 1) / (2 * n)) ∧
    ∃ (C : ℝ) (k : ℕ) (κ : ℝ), 0 < C ∧ 0 < κ ∧ κ ≤ 1 ∧
      (∃ A : BitMachine, ∀ (d : ℕ) (Mq : Matrix (Fin d × Fin d) (Fin d × Fin d) (ℚ × ℚ)) (ε : ℚ),
        1 ≤ d → 0 < ε → ε ≤ 1 → (Mq.map ratC).PosSemidef → (1 - Mq.map ratC).PosSemidef →
          ∃ (q : ℚ) (T : ℕ), A.OutputsWithin (encNat d ++ encRat ε ++ encMat Mq) (encRat q) T ∧
            |(q : ℝ) - supportFn (sepAB d d) (Mq.map ratC)| ≤ ε ∧
            (T : ℝ) ≤ subexpBound C k (encNat d ++ encRat ε ++ encMat Mq).length d ε) ∧
      (∃ A : BitMachine, ∀ (d : ℕ) (Mq : Matrix (Fin d × Fin d) (Fin d × Fin d) (ℚ × ℚ)) (c s : ℚ),
        1 ≤ d → 0 ≤ s → s < c → c ≤ 1 → (Mq.map ratC).PosSemidef → (1 - Mq.map ratC).PosSemidef →
          ∃ (b : Bool) (T : ℕ), A.OutputsWithin (encNat d ++ encRat c ++ encRat s ++ encMat Mq) [b] T ∧
            ((c : ℝ) ≤ supportFn (sepAB d d) (Mq.map ratC) → b = true) ∧
            (supportFn (sepAB d d) (Mq.map ratC) ≤ s → b = false) ∧
            (T : ℝ) ≤ subexpBound C k (encNat d ++ encRat c ++ encRat s ++ encMat Mq).length d
              (κ * ((c : ℝ) - s))) := by sorry

end Supplement

end ArgmaxDeFinetti
