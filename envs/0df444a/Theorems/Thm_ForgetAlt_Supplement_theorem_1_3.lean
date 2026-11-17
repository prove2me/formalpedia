-- Prove2me | Theorems.Thm_ForgetAlt_Supplement_theorem_1_3
-- name    : ForgetAlt.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:18:33.488629+00:00
-- url     : https://prove2.me/theorems/37aad30c-6bc8-457a-8510-293e68c0c51b
-- title:
--   Theorem 1.3: $(1-\varepsilon)$-approximate maximum matching in $O(\varepsilon^{-4}\log(\varepsilon^{-2}n))$ CONGEST rounds and in $O(\varepsilon^{-4})$ semi-streaming passes with $O(n\log n)$ bits
-- statement:
--   Let $G$ be a graph with $n$ vertices, $\mu(G)$ the size of its maximum matching and $\varepsilon\in(0,1)$.
--
--   1. **CONGEST.** There is a randomized distributed algorithm in the CONGEST model that computes a matching of $G$ of size at least $(1-\varepsilon)\mu(G)$ within
--   $$O\big(\varepsilon^{-4}\log(\varepsilon^{-2}n)\big)$$
--   rounds, with high probability: for every fixed constant $b>0$ the failure probability is at most $n^{-b}$, the constant in the round bound depending on $b$.
--   2. **Semi-streaming.** There is a deterministic multi-pass semi-streaming algorithm that computes a matching of $G$ of size at least $(1-\varepsilon)\mu(G)$ with
--   $$O(\varepsilon^{-4})\ \text{passes and}\ O(n\log n)\ \text{bits of memory},$$
--   for an arbitrary edge order that may change between passes.
--
--   The CONGEST bound improves the previous $\tilde O(\varepsilon^{-10})$ rounds, and the streaming bound is obtained from the same double path framework.
--
--   **Formalization Note** The CONGEST clause quantifies over every identifier range $[0,n^\kappa)$, every connected simple graph, every injective identifier assignment and every known value $N$ with $n\le N\le n^\kappa$ (the vertices know $n$ or a polynomial upper bound on it); the round budget depends only on $(N,\varepsilon)$, the bounds are in the true $n$, and the failure bound is on the outer measure of the set of failing coin tapes. The streaming clause gives one machine per $(n,\varepsilon)$ with memory at most $c\,n(\lfloor\log_2 n\rfloor+1)$ bits and at most $C\varepsilon^{-4}$ passes, $c$ and $C$ absolute.
--
--   Differences from the source:
--   - reading: “runs in the CONGEST model” (p.34) → a CongestAlg: one program run by every vertex, arbitrary local state, initial state from (n, ε), its identifier, its neighbours' identifiers and a private fair-coin tape; per round one message per neighbour, of which the first bandwidth·(⌊log₂ n⌋ + 1) bits are delivered (bandwidth a constant of the algorithm); messages received labelled by sender; a round budget R(n, ε); each vertex finally reports its partner's identifier or none; G simple and connected; reason: operational rendering of the model of p.34; knowing the neighbours' identifiers (KT1) costs at most one extra round in a KT0 reading, absorbed by the constant
--   - encoding: “Vertices and edges are uniquely identified by O(log n)-bit integer values” → for every fixed κ, every injective identifier assignment into [0, n^κ) (the algorithm may depend on κ); an edge is identified by its endpoints' identifiers; reason: O(log n)-bit integers are exactly the values below n^κ for a constant κ; edge identifiers carry no information beyond the endpoint pair
--   - reading: “all vertices know n, or a common polynomial upper bound on n” → all vertices know ε and a value N with n ≤ N ≤ n^κ (N = n included); the round budget is R(N, ε) and the bounds are in the true n; reason: both cases of the model's assumption (p.49, “If only a common polynomial upper bound on n is known, it can be used in this normalization and in the round budgets”); ε is the input accuracy (the paper's ε = 2^{−x} is a WLOG step of the proof, p.48), so ε is any real in (0, 1)
--   - reading: “succeeds with high probability” (= probability ≥ 1 − n^{−b} for any fixed b > 0, the round constant depending on b, p.4) → ∀ b > 0, ∃ algorithm and C such that the set of coin tapes on which the run fails has outer measure ≤ n^{−b} under the product of fair coins; reason: the definition on p.4; outer measure of the failure set is the conservative reading
--   - reading: O(ε^{−4} log(ε^{−2} n)) rounds → R(n, ε) ≤ C·ε^{−4}·(ln(ε^{−2} n) + 1); reason: ln(ε^{−2} n) ≥ ln 2 for n ≥ 2, so the + 1 changes only the constant; it keeps the bound positive at n = 1, where the paper calls the problem trivial
--   - encoding: “(1 − ε)-approximation maximum matching” → the reports are consistent (u reports v iff v reports u, every report names a vertex) and the reported pairs form a matching M of G with (1 − ε)·µ(G) ≤ |M| (IsMatchingIn, matchingNumber of the published LoadBalMatch_Main_Matching); in streaming, the output set is such a matching; reason: standard meaning of a (1 − ε)-approximate matching, p.48
--   - reading: “deterministic … in the semi-streaming model with O(ε^{−4}) passes and O(n log n)-bit memory” (model of p.34) → constants C, c and, for each n and ε, a deterministic StreamMachine with s(n, ε) ≤ c·n·(⌊log₂ n⌋ + 1) bits of state (Fin 2^s, every retained bit counted) making P(n, ε) ≤ C·ε^{−4} passes, correct for every graph on Fin n and every family of edge streams (one per pass, orders arbitrary and possibly different between passes); reason: the usual information-theoretic multi-pass streaming model; the machine may depend on (n, ε) but the constants may not
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Theorem 1.3, printed p.51 (PDF p.52); also stated on printed p.4 (PDF p.5); models: Section 3.7, printed p.34 (PDF p.35)

import Mathlib
import Definitions.Def_ForgetAlt_Supplement_Congest
import Definitions.Def_ForgetAlt_Supplement_SemiStream

namespace ForgetAlt.Supplement

open LoadBalMatch.Main

/-- **Theorem 1.3**, printed p.51 (PDF p.52; also stated on printed p.4). Izumi–Kitamura–Yamaguchi,
*Forgetting Alternation and Blossoms*, STOC 2027 submission (manuscript sha256 b656488c…).

"There exists: • a randomized `(1 − ε)`-approximation maximum matching algorithm for a given graph
`G` which runs in the CONGEST model in `O(ε⁻⁴ log(ε⁻²n))` rounds and succeeds with high
probability. • a deterministic `(1 − ε)`-approximation maximum matching algorithm for a given graph
`G` which runs in the semi-streaming model with `O(ε⁻⁴)` passes and `O(n log n)`-bit memory."

"With high probability" (p.4): with probability at least `1 − n^{−b}` for any fixed constant
`b > 0`, the constant in the round bound depending on `b`.

**Formalization Note.**
1. CONGEST (`CongestAlg`, model of p.34): for every identifier range exponent `κ` and every
   `b > 0` there are an algorithm (with its bandwidth constant) and a constant `C` such that for
   every connected simple graph `G` on `Fin n`, every injective identifier assignment into
   `[0, n^κ)`, every value `N` with `n ≤ N ≤ n^κ` known to all vertices ("all vertices know n, or
   a common polynomial upper bound on n", p.34; `N = n` is the first case) and every
   `ε ∈ (0, 1)`, the algorithm stops after at most
   `C·ε⁻⁴·(ln(ε⁻²n) + 1)` rounds, and the coin tapes on which its reports are not a matching of
   `G` with at least `(1 − ε)µ(G)` edges have (outer) measure at most `n^{−b}`. The `+ 1` keeps
   the bound positive at `n = 1`; for `n ≥ 2` it changes only the constant.
2. Semi-streaming (`StreamMachine`, model of p.34): there are constants `C, c` and, for every `n`
   and `ε`, a deterministic machine with `s(n, ε) ≤ c·n·(⌊log₂ n⌋ + 1)` bits of memory making
   `P(n, ε) ≤ C·ε⁻⁴` passes, whose output, for every graph `G` on `Fin n` and every family of
   edge streams of `G` (one per pass, orders arbitrary), is a matching of `G` with at least
   `(1 − ε)µ(G)` edges. -/
theorem theorem_1_3 :
    (∀ (κ : ℕ) (b : ℝ), 0 < b → ∃ (A : CongestAlg) (C : ℝ),
      ∀ (n N : ℕ) (G : SimpleGraph (Fin n)) (ident : Fin n → ℕ),
        G.Connected → Function.Injective ident → (∀ v, ident v < n ^ κ) → n ≤ N → N ≤ n ^ κ →
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          (A.rounds N ε : ℝ) ≤ C * ε⁻¹ ^ 4 * (Real.log (ε⁻¹ ^ 2 * n) + 1) ∧
          tapeMeasure n {ω | ¬ A.Succeeds G ident ε N ω} ≤ ENNReal.ofReal ((n : ℝ) ^ (-b))) ∧
    (∃ (C c : ℝ) (s P : ℕ → ℝ → ℕ) (A : (n : ℕ) → (ε : ℝ) → StreamMachine n (s n ε)),
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
        (P n ε : ℝ) ≤ C * ε⁻¹ ^ 4 ∧
        (s n ε : ℝ) ≤ c * n * (Nat.log 2 n + 1) ∧
        ∀ (G : SimpleGraph (Fin n)) (σ : ℕ → List (Sym2 (Fin n))),
          (∀ i, IsEdgeStream G (σ i)) →
            IsMatchingIn G ((A n ε).run (P n ε) σ) ∧
            (1 - ε) * (matchingNumber G : ℝ) ≤ (((A n ε).run (P n ε) σ).card : ℝ)) := by sorry

end ForgetAlt.Supplement
