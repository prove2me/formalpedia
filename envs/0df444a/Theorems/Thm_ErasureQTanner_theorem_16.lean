-- Prove2me | Theorems.Thm_ErasureQTanner_theorem_16
-- name    : ErasureQTanner.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:03:46.813907+00:00
-- url     : https://prove2.me/theorems/9c4c1dac-91ca-4042-82b1-cfd969e4a0ca
-- title:
--   Theorem 16 with Theorem 2 — rate $1-2\rho-\varepsilon$ quantum Tanner codes decoding $\rho$-erasures in linear time
-- statement:
--   For every $\rho\in(0,\frac12)$ and every $\varepsilon>0$ there exist a degree $\Delta$, inner codes $C_A,C_B,D_A,D_B$ with check bases, a constant $a>0$, a decoder program $P$, a word-size constant $b$, and a family of quadripartite square complexes $(G_i,A_i,B_i)$ with $|G_i|$ strictly increasing, such that every member, of length $N=|G_i|\Delta^2$, satisfies:
--
--   1. it is a CSS code: $H_XH_Z^{\mathsf T}=0$;
--   2. its rate is at least $1-2\rho-\varepsilon$: $(1-2\rho-\varepsilon)N\le N-\mathrm{rank}H_X-\mathrm{rank}H_Z$;
--   3. every row of $H_X,H_Z$ has weight at most $\Delta^2$, and every qubit lies in at most $4\Delta^2$ rows;
--   4. its distance is at least $aN$: every word of $C_Z\setminus C_X^\perp$ and of $C_X\setminus C_Z^\perp$ has weight at least $aN$;
--   5. $\Pr_{\varepsilon\sim\rho}[\mathrm{decode}(\mathcal C,\varepsilon)=1]\ge1-2^{-aN}$;
--   6. on every input, $P$ halts within $N/a$ steps with bit outputs, on a word RAM with $b(\lfloor\log_2|G_i|\rfloor+1)$-bit words or more;
--   7. with probability at least $1-2^{-aN}$ over the erasure pattern, for all errors $e_X,e_Z$ on the pattern, $P$ outputs $e'_Z\in e_Z+C_Z^\perp$ and $e'_X\in e_X+C_X^\perp$.
--
--   The capacity of the quantum erasure channel is $1-2\rho$, so this says that these bounded-weight codes with linear distance reach it with a linear-time decoder and exponentially small failure.
--
--   Differences from the source:
--   - generalization: Theorem 16: $\varepsilon\in(0,1-2\rho)$ → every $\varepsilon>0$, as in Theorem 2; reason: for $\varepsilon\ge1-2\rho$ take the code of a smaller gap; the statement at $\varepsilon<1-2\rho$ is exactly Theorem 16
--   - reading: "decoding time $\le N/a$" → at most $N/a$ steps of one program $P$ on the published word RAM with $W\ge b(\lfloor\log_2|G|\rfloor+1)$, on every input; reason: the paper names no machine, and its model needs constant-time look-ups; Theorem 16 states the time without a probability, and a clocked program achieves it
--   - reading: the code is known to the decoder → the group tables are preloaded input, $\Delta$ and the local codes are in $P$; reason: one program serves the whole family
--   - encoding: "for all $N>N_0$" → a sequence of complexes with $|G_i|$ strictly increasing; reason: $N=|G|\Delta^2$ exists only at some lengths; the paper itself speaks of a family of increasing length (p.12)
--   - encoding: generating sets in $G$ → labelled generators $\mathrm{Fin}\,\Delta\hookrightarrow G_i$ and local codes on $\mathrm{Fin}\,\Delta$; reason: the local codes are fixed across the family (p.4)
--   - reading: "decode" with an average over the Pauli errors on p.4 → clause 7 holds for all errors on the pattern, and the probability is over the pattern only; reason: it implies the average; the paper's own proof has a failure event depending on the pattern only
--   - reading: Theorem 2: "constant stabilizer weights and qubit degrees" → $\Delta^2$ and $4\Delta^2$; reason: the constants of the construction: four local views of at most $\Delta^2$ generators each
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), Theorem 16, p.27; Theorem 2, p.3

import Mathlib
import Definitions.Def_ErasureQTanner_HX
import Definitions.Def_ErasureQTanner_inputWords
import Definitions.Def_ErasureQTanner_noisyProb

set_option autoImplicit false

namespace ErasureQTanner

/-- **Theorem 16, with Theorem 2.** Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.27: "Consider any `ρ ∈ (0, 1/2)` and any `ε ∈ (0, 1 − 2ρ)`. Then there exists positive constants `a, ∆, N₀`
(i.e. depending only on `ρ` and `ε`) such that for all `N > N₀`, the family of quantum Tanner codes `{C_{ρ,ε,∆,N}}` has rate at least `1 − 2ρ − ε` and can decode random
quantum erasures of rate `ρ` with probability `Pr_{ε∼ρ}[decode(C_{ρ,ε,∆,N}, ε) = 1] ≥ 1 − 2^{−aN}`. and decoding time `≤ N/a`." p.3 (Theorem 2): any `ε > 0`; "the degree and the local
codes are fixed independently of `N`"; "constant stabilizer weights and qubit degrees with minimum distance growing linearly with `N`".

**Formalization Note.** The erasure pattern is `x`, since `ε` is the rate gap. `Δ`, the local codes and bases, `a`, the program `P`, `b` come before the family `Γ`. The family is a sequence with
`|G_i|` strictly increasing, since `N = |G|∆²` exists only at some lengths, so "`N > N₀`" is a dropped prefix. "Constant" weights are `∆²` and `4∆²` (four local views, each with at most `∆²` generators). "Decoding time" is on the published word RAM `TrulySubcubicAPSP`, with
`b(⌊log₂|G|⌋ + 1)`-bit words and more; the input (`inputWords`) has the group tables, the pattern and the syndromes, never the errors. The clauses are, in order: `H_X H_Zᵀ = 0`;
rate; row weights; qubit degrees; distance `≥ aN` by its two defining bounds; `decode = 1`; halting within `N/a` steps with bit outputs on every input; correct cosets. The last probability is over the erasure only, for all errors on the pattern, which implies p.4's average over the Pauli errors. -/
theorem theorem_16 (ρ ε : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hε : 0 < ε) :
    ∃ (Δ : ℕ) (L : LocalCodes Δ) (a : ℝ) (P : List TrulySubcubicAPSP.Instr) (b : ℕ) (Γ : ℕ → LRData Δ),
      0 < a ∧ StrictMono (fun i => Fintype.card (Γ i).G) ∧
      ∀ C ∈ Set.range Γ,
        (HX C L) * (HZ C L).transpose = 0 ∧
        (1 - 2 * ρ - ε) * C.N ≤ (C.N : ℝ) - (HX C L).rank - (HZ C L).rank ∧
        (∀ r, hammingNorm (HX C L r) ≤ Δ ^ 2) ∧ (∀ r, hammingNorm (HZ C L r) ≤ Δ ^ 2) ∧
        (∀ s : C.Square, (Finset.univ.filter fun r => HX C L r s ≠ 0).card +
          (Finset.univ.filter fun r => HZ C L r s ≠ 0).card ≤ 4 * Δ ^ 2) ∧
        (∀ w ∈ checkKer (HZ C L), w ∉ checkRows (HX C L) → a * C.N ≤ (hammingNorm w : ℝ)) ∧
        (∀ w ∈ checkKer (HX C L), w ∉ checkRows (HZ C L) → a * C.N ≤ (hammingNorm w : ℝ)) ∧
        1 - (2 : ℝ) ^ (-(a * C.N)) ≤ noisyProb ρ (cssDecodes (HX C L) (HZ C L)) ∧
        (∀ (x : C.Square → Bool) (eX eZ : C.Square → ZMod 2), SupportedOn eX x → SupportedOn eZ x →
          ∀ W : ℕ, b * (Nat.log2 (Fintype.card C.G) + 1) ≤ W →
            ∃ (t : ℕ) (e'X e'Z : C.Square → ZMod 2), (t : ℝ) ≤ C.N / a ∧
              RunOutput C L P W t x eX eZ e'X e'Z) ∧
        1 - (2 : ℝ) ^ (-(a * C.N)) ≤ noisyProb ρ (fun x : C.Square → Bool =>
          ∀ eX eZ : C.Square → ZMod 2, SupportedOn eX x → SupportedOn eZ x →
          ∀ W : ℕ, b * (Nat.log2 (Fintype.card C.G) + 1) ≤ W →
            ∃ (t : ℕ) (e'X e'Z : C.Square → ZMod 2), RunOutput C L P W t x eX eZ e'X e'Z ∧
              e'Z + eZ ∈ checkRows (HZ C L) ∧ e'X + eX ∈ checkRows (HX C L)) := by sorry

end ErasureQTanner
