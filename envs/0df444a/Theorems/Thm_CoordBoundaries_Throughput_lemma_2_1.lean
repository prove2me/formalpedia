-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_lemma_2_1
-- name    : CoordBoundaries.Throughput.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:39:32.513044+00:00
-- url     : https://prove2.me/theorems/983d7ca9-5110-4b8f-874d-85047ae67c73
-- title:
--   Lemma 2.1 — candidate partitions with a nearly optimal reference schedule, and exact solution of small optima
-- statement:
--   There are an absolute constant $c$ and a polynomial $p$ such that the following holds for every number of machines $m\ge1$ and every $\eta=1/q$ with $q\ge100$. There is a positive integer $K_0$, depending only on $m$ and $\eta$; put
--   $$\Gamma=\frac{2K_0}{\eta^7},\qquad H=\lceil 5K_0\Delta\Gamma^q\rceil .$$
--
--   1. If $\mathrm{OPT}\ge H$, a deterministic construction with running time polynomial in the input length and $\Delta$ (for fixed $m,\eta$) outputs at most $q$ candidate partitions $(\mathcal B,\mathcal S)$, each with an integer bound $1\le K\le\Delta\Gamma^q$, and at least one candidate admits a feasible aligned schedule $O'$ with (a) $|O'|\ge(1-2\eta)\mathrm{OPT}$; (b) every execution in an eligible block; (c) at most $K$ executions per block across all machines; (d) $|O'|\ge m\Delta|\mathcal B|/\eta$ and $|O'|\ge K|\mathcal S|/\eta^8$.
--   2. If $\mathrm{OPT}<H$, the instance can be solved exactly in running time $n^{cH}\mathrm{poly}(N)$, and also in running time $(2m)^{cH}\mathrm{poly}(n,T,N)$.
--
--   Here $\Delta\ge1$ is an integer given with the instance. The lemma produces the partitions on which the configuration relaxation is solved; the exact routine handles instances with small optimum.
--
--   **Formalization Note** Programs read the instance followed by $\Delta$. The exact-case budgets are $\max(1,n)^{cH}p(N+\sigma(\Delta))$ and $(2m)^{cH}p(n+T+N+\sigma(\Delta))$, with $\sigma(\Delta)$ the bit size of $\Delta$; "solved exactly" means the output is a feasible schedule of cardinality $\mathrm{OPT}$.
--
--   Differences from the source:
--   - encoding: "a computable positive integer K0 depending only on m, η" → ∃ K₀ ≥ 1 chosen after m and q; reason: every single integer is computable; dependence only on m, η is the quantifier order
--   - encoding: Γ = 2K0/η^7 and H = ⌈5K0∆Γ^q⌉ → Γ = 2K₀q^7 and H = 5K₀∆Γ^q in ℕ; reason: η = 1/q makes both integers (p. 28)
--   - reading: "a construction with running time polynomial in the input length and ∆, for fixed m, η" → one deterministic program per (m, q) with cost at most p_c(N + ∆) on input (I, ∆), whenever OPT ≥ H; reason: the construction of Appendix A is greedy and makes no random choices; the statement is conditional on OPT ≥ H as printed
--   - encoding: candidate partitions with their bounds K → the output equals the encoding of a list of (breakpoints, superblock labels, K); reason: output format of a program
--   - generalization: "an integer bound K ≤ ∆Γ^q" → 1 ≤ K ≤ ∆Γ^q; reason: Appendix A, p. 29, gives K_ℓ = 2∆K₀Γ^{ℓ−1} ≥ 1; the stronger conclusion implies the printed one
--   - reading: "n^{O(H)} poly(N) or (2m)^{O(H)} poly(n, T, N)" → an absolute c and polynomial p chosen before m and q; budgets max(1,n)^{cH}·p(N + σ(∆)) and (2m)^{cH}·p(n + T + N + σ(∆)); reason: the O(H) constant and the polynomial are not subscripted by m or η; σ(∆) accounts for reading ∆, and max(1,·) only matters at n = 0
--   - reading: "the instance can be solved exactly" → the output is a feasible schedule with OPT jobs; reason: this is what solving the maximization problem exactly means
--   - encoding: "polynomial time" / "pseudopolynomial time" for an algorithm → one program of the published unit-cost integer RAM `CongruencyTU` and a bit-length polynomial, fixed before the input; every run halts within the stated cost and keeps every register within q(input bit size) bits; reason: unit-cost arithmetic on polynomially many bits equals bit cost up to polynomial factors
--   - generalization: the residual instance after discarding individually infeasible jobs in §2, with positive machine count and configuration cap → also permits jobs with processing time exceeding their window length; reason: individually infeasible jobs occur in no feasible configuration or schedule; the extra zero cases have only empty configurations or zero marginals, and every source instance is included
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), p. 9, Lemma 2.1 (proof: Appendix A, pp. 28–29)

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Partition

open Classical CongruencyTU

namespace CoordBoundaries.Throughput

/-- **Lemma 2.1** (Tong–Xu, p. 9). There are an absolute exponent constant `c` and polynomial `p`
such that for every number of machines `m ≥ 1` and every `η = 1/q` with `q ≥ 100` there is a
positive integer `K₀`, depending only on `m, q`; put `Γ = 2K₀/η⁷ = 2K₀q⁷` and
`H(∆) = ⌈5K₀∆Γ^q⌉ = 5K₀∆Γ^q`.

* (Construction.) A deterministic program, on input `(I, ∆)` with `I.m = m` and an integer `∆ ≥ 1`,
  runs, whenever `OPT ≥ H(∆)`, in time polynomial in the input length and `∆`, and outputs at most
  `q` candidates `(ℬ, 𝒮, K)` with `1 ≤ K ≤ ∆Γ^q`, at least one of which admits a feasible aligned
  schedule `O′` satisfying (a)–(d).
* (Exact case.) If `OPT < H(∆)`, two deterministic programs solve the instance exactly, in time
  `max(1,n)^{c·H} · p(N)` and `(2m)^{c·H} · p(n + T + N)` respectively. -/
theorem lemma_2_1 :
    ∃ (c : ℕ) (p : Polynomial ℕ), ∀ m : ℕ, 1 ≤ m → ∀ q : ℕ, 100 ≤ q →
      ∃ K₀ : ℕ, 1 ≤ K₀ ∧
        (∃ (Pc : Program) (pc qc : Polynomial ℕ), ∀ I : Instance, I.Valid → I.m = m →
          ∀ Δ : ℕ, 1 ≤ Δ → 5 * K₀ * Δ * (2 * K₀ * q ^ 7) ^ q ≤ OPT I →
            RunBounded Pc noOracle noCoins (enc I ++ [(Δ : ℤ)]) (pc.eval (N I + Δ)) qc 0 ∧
            ∃ cs : List (Partition I.T × ℕ),
              outputAfter Pc noOracle noCoins (enc I ++ [(Δ : ℤ)]) (pc.eval (N I + Δ)) =
                encCands cs ∧
              cs.length ≤ q ∧
              (∀ cd ∈ cs, 1 ≤ cd.2 ∧ cd.2 ≤ Δ * (2 * K₀ * q ^ 7) ^ q) ∧
              ∃ cd ∈ cs, ∃ O : Sched I, cd.1.Certifies q Δ cd.2 O) ∧
        (∃ (P₁ P₂ : Program) (q₁ q₂ : Polynomial ℕ), ∀ I : Instance, I.Valid → I.m = m →
          ∀ Δ : ℕ, 1 ≤ Δ → OPT I < 5 * K₀ * Δ * (2 * K₀ * q ^ 7) ^ q →
            (RunBounded P₁ noOracle noCoins (enc I ++ [(Δ : ℤ)])
                ((max 1 I.n) ^ (c * (5 * K₀ * Δ * (2 * K₀ * q ^ 7) ^ q)) *
                  p.eval (N I + bitSize [(Δ : ℤ)])) q₁ 0 ∧
              SolvesExactly I (outputAfter P₁ noOracle noCoins (enc I ++ [(Δ : ℤ)])
                ((max 1 I.n) ^ (c * (5 * K₀ * Δ * (2 * K₀ * q ^ 7) ^ q)) *
                  p.eval (N I + bitSize [(Δ : ℤ)])))) ∧
            (RunBounded P₂ noOracle noCoins (enc I ++ [(Δ : ℤ)])
                ((2 * m) ^ (c * (5 * K₀ * Δ * (2 * K₀ * q ^ 7) ^ q)) *
                  p.eval (I.n + I.T + N I + bitSize [(Δ : ℤ)])) q₂ 0 ∧
              SolvesExactly I (outputAfter P₂ noOracle noCoins (enc I ++ [(Δ : ℤ)])
                ((2 * m) ^ (c * (5 * K₀ * Δ * (2 * K₀ * q ^ 7) ^ q)) *
                  p.eval (I.n + I.T + N I + bitSize [(Δ : ℤ)]))))) := by sorry

end CoordBoundaries.Throughput
