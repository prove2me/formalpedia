-- Prove2me | Theorems.Thm_DynColorWC_Main_theorem_2
-- name    : DynColorWC.Main.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:48:31.57509+00:00
-- url     : https://prove2.me/theorems/e288938e-6417-457a-8ee5-f32c480968c2
-- title:
--   Theorem 2 — a smooth dynamic ε-almost-clique decomposition in poly(1/ε) log³ n worst-case time w.h.p., with recourse properties 1–3
-- statement:
--   Let $\varepsilon\in(0,1/100)$, $n\ge2$ and $\Delta\ge\mathrm{poly}(1/\varepsilon,\log n)$. There is a randomized algorithm that maintains, w.h.p., a smooth $\varepsilon$-almost-clique decomposition (Definition 4.1) of every dynamic $n$-vertex graph of maximum degree $\Delta$ undergoing up to $\mathrm{poly}(n)$ oblivious edge updates, with the recourse properties
--   1. for $\rho=\Theta(\varepsilon^2\Delta)$: whenever $\ell(i)$ is set to Reg, $z(C_i)\ge\rho$;
--   2. the recourse of $\tilde A$ and $\tilde E$ during one update is $\mathrm{poly}(1/\varepsilon)\log^2n$;
--   3. there is $\eta=\Theta_\varepsilon(\log^2n/\Delta)$ such that for all times $\tau'\le\tau$: (a) the recourse of the vertex partition over $[\tau',\tau]$ is at most $2+\eta(\tau-\tau')$; (b) for every $v\notin B$ throughout $[\tau',\tau]$, with $h(v)$ the number of updates of $[\tau',\tau]$ incident on $v$, the recourse of $\tilde A(v)$ and $\tilde E(v)$ over $[\tau',\tau]$ is at most $4+\eta(\tau-\tau')+h(v)$; (c) if $C(v)$ changes at time $\tau$, then for at least $1/\eta$ updates of $[\tau\pm1/\eta]$ we had $v\in B$;
--
--   and its worst-case update time is $\mathrm{poly}(1/\varepsilon)\log^3n$ w.h.p.
--
--   In Lean: absolute constants for Part 1 and for $\rho$; the threshold and the $\mathrm{poly}(1/\varepsilon)$ factors with coefficients fixed before $\varepsilon$; then for each $\varepsilon$ and all $c,d>0$ one program and $\eta$ (w.h.p. as in §3: the algorithm's constants may depend on the failure exponents); for every $n\ge2$, every $\Delta$ above the threshold and every legal sequence of at most $n^d$ updates fixed before the coin tape, the tapes on which some clause fails at some time have measure at most $n^{-c}$. The structure is the one the machine writes.
--
--   Differences from the source:
--
--   - encoding: machine model not specified (§3: set and map operations in O(log |S|) worst-case time, uniform random choices) → the published DynBrooks word RAM (unit-cost uniform random words, a read that blocks until an operation is delivered, every instruction one step) with word size a·⌈log₂(n+1)⌉, the program and a fixed before n, Δ and the sequence; reason: the standard word-RAM reading of §3; a blocking read gives per-update worst-case time and rules out look-ahead
--   - encoding: Δ, an upper bound on the maximum degree known to the algorithm → preprocessing receives the words n and min(Δ, 2n); reason: Δ may exceed every word; min(Δ, 2n) determines Δ whenever Δ ≤ 2n, and for Δ > 2n every degree is below Δ/2, so every vertex is sparse and nothing depends on the exact Δ
--   - encoding: the graph starts empty (§3) and undergoes legal edge updates (degree at most Δ at every moment) → IsLegalSeq Δ σ: from the empty graph on Fin n, each update inserts a non-edge uv (u ≠ v) or deletes an edge, and leaves every degree ≤ Δ; times 0, …, |σ| are the completed states after preprocessing and after each update; reason: §3 dynamic graphs model; no condition beyond the degree bound
--   - reading: 'w.h.p.' and 'up to poly(n) oblivious edge updates' → as in §3: ∀ ε, ∀ c, d > 0 ∃ program (it may depend on ε, c, d, not on n, Δ or σ): for every n ≥ 2, Δ above the threshold and legal σ with |σ| ≤ n^d fixed before the coin tape, the tapes on which some clause fails have measure ≤ n^{−c}; every clause holds at every time inside this one event; reason: §3 (p. 13) defines w.h.p. as probability 1 − 1/poly(n) over poly(n) updates, for a desirably large polynomial, so the algorithm's constants are set by the failure exponents (its samplers use O(ε⁻² ln n) probes, Lemma 4.13; L in Eq. (2)); Theorem 2 itself orders Let ε, n, Δ before there is a randomized algorithm maintaining, w.h.p.; a program uniform in n, Δ and the sequence is stronger than the page
--   - encoding: Δ ⩾ poly(1/ε, log n) → Δ ≥ Kth(c,d)·(1/ε)^a·(log₂ n)^b with a, b and the function Kth fixed before ε; reason: a polynomial in 1/ε and log n whose coefficient may depend on the failure exponents c, d
--   - encoding: worst-case update time poly(1/ε) log³ n w.h.p.; recourse of Ã, Ẽ during one update poly(1/ε) log² n → K(c,d)·(1/ε)^m·(log₂ n)^3 steps per update and K(c,d)·(1/ε)^m·(log₂ n)^2 for the total recourse of Ã and Ẽ (summed over vertices) at each update, with m and K fixed before ε; reason: poly(1/ε) with coefficients independent of ε
--   - encoding: the data structure the algorithm keeps (C, the explicit inverse map i ↦ C_i, Ã, Ẽ, ℓ, z, B, I_B; Definition 4.1) → the machine's own change log of four-word records (tags 0–6) applied to the initial structure (all ⊥, ∅, Irr, 0); z(i) is reported as a rational b/c; C_i is read off C; reason: explicit maintenance as for the coloring; z(C_i) is rational; the inverse map is determined by C
--   - encoding: Ω(ε²Δ)-sparse (Definition 4.1 Part 1); ρ = Θ(ε²Δ) (property 1) → cSp·ε²·Δ-sparse and z(C_i) ≥ cρ·ε²·Δ with absolute cSp, cρ > 0 fixed before ε; reason: absolute constants; a larger ρ only strengthens property 1, so only its lower bound carries content
--   - encoding: each regular C_i has z(C_i) = z(i) (Part 2) → z(C_i) = z(i) for nonempty regular C_i; the ε-almost-clique condition for every regular C_i; reason: z(∅) is undefined (division by |C| = 0); Lemma 4.36 maintains z(i) for C_i ≠ ∅
--   - encoding: there exists η = Θ_ε(log² n/Δ) → a function η(n, Δ) chosen with the program (after ε, c, d; before n, Δ and the sequence) with c₁ log₂² n/Δ ≤ η ≤ c₂ log₂² n/Δ for n ≥ 2, Δ ≥ 1, where 0 < c₁ ≤ c₂ depend on ε (and, with the program, on c, d); reason: both directions of Θ_ε; η is a parameter of the algorithm (Eq. (2)), built from L, whose constant the failure exponent sets
--   - encoding: times τ′ ≤ τ, updates [τ′, τ], 'whenever ℓ(i) is set to Reg', 'v ∉ B throughout [τ′, τ]', h(v) → updates are numbered 1, …, |σ| and update t leads from completed state t − 1 to t; sums run over t ∈ [τ′, τ] with τ′ ≥ 1; ℓ(i) is set to Reg at t when it is Reg at t and not before (for t = 0: initially Irr); v ∉ B at the states τ′, …, τ; h(v) counts the updates t ∈ [τ′, τ] with v an endpoint; reason: Definition 4.3's sums compare consecutive states
--   - reading: (c) if C(v) changes at time τ, then for at least 1/η updates of [τ ± 1/η] we had v ∈ B → for every τ ∈ [1, |σ|] with C_τ(v) ≠ C_{τ−1}(v) and τ + 1/η ≤ |σ|: the number of times t ∈ [0, |σ|] with |t − τ| ≤ 1/η and v ∈ B_t is at least 1/η; reason: the window must exist: when the sequence ends right after τ, the later half of [τ ± 1/η] is not part of the run, and no online algorithm can be required to have spent it in B
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Theorem 2, p. 17 (PDF 19)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynColorWC_Main_Model
import Definitions.Def_DynColorWC_Main_AlmostClique
import Definitions.Def_DynColorWC_Main_Decomposition

namespace DynColorWC.Main

open Classical in
/-- **Theorem 2** (Flin and Ghaffari (2026), STOC 2027 submission, sha256 93ebb2ff…3154300e3,
p. 17 (PDF 19)). Let `ε ∈ (0, 1/100)`, `n ≥ 2`, and `Δ ≥ poly(1/ε, log n)`. There is a randomized
algorithm maintaining, w.h.p., a smooth `ε`-almost-clique decomposition (Definition 4.1) for all
dynamic `n`-vertex graphs of maximum degree `Δ` undergoing up to `poly(n)` oblivious edge updates,
with the recourse properties
1. for `ρ = Θ(ε²Δ)`, whenever `ℓ(i)` is set to `Reg`, `z(C_i) ≥ ρ`;
2. the recourse of `Ã` and `Ẽ` during one update is `poly(1/ε) log² n`;
3. there is `η = Θ_ε(log² n / Δ)` such that for all times `τ' ≤ τ`:
   (a) the recourse of the vertex partition over `[τ', τ]` is at most `2 + η(τ − τ')`;
   (b) for all `v ∉ B` throughout `[τ', τ]`, with `h(v)` the number of updates of `[τ', τ]` incident
   on `v`, the recourse of `Ã(v)` and `Ẽ(v)` over `[τ', τ]` is at most `4 + η(τ − τ') + h(v)`;
   (c) for all `v`, if `C(v)` changes at time `τ`, then for at least `1/η` updates of `[τ ± 1/η]`
   we had `v ∈ B`;
and worst-case update time `poly(1/ε) log³ n` w.h.p.

Formal reading. Absolute constants `cSp` (Part 1, "`Ω(ε²Δ)`-sparse") and `cρ` (`ρ ≥ cρ ε² Δ`);
the polynomial threshold `Kth(c,d)·(1/ε)^a·(log₂ n)^b` and the `poly(1/ε)` factor `K(c,d)·(1/ε)^m`
are fixed before `ε`. "W.h.p." is read as in §3 (p. 13: probability `1 − 1/poly(n)` over `poly(n)`
updates, "for a desirably large polynomial"): for every `ε` and all `c, d > 0` there are a program
`P` (it may depend on `ε, c, d`, but not on `n`, `Δ` or the sequence), its word-size constant, and
`η(n, Δ)` with `c₁ log₂² n/Δ ≤ η ≤ c₂ log₂² n/Δ`, such that for every `n ≥ 2`, every `Δ` above
the threshold and every legal sequence `σ` from the empty graph with at most `n^d` updates, fixed
before the coin tape, the tapes on which some clause fails have measure at most `n^{-c}`. The
decomposition is the one the machine writes (`decompAt`); preprocessing receives `n, min Δ (2n)`.
Times are completed states `0, …, |σ|` (after preprocessing and `t` updates); update `t ≥ 1`
leads from time `t − 1` to time `t`. -/
theorem theorem_2 :
    ∃ (cSp cρ : ℝ), 0 < cSp ∧ 0 < cρ ∧
    ∃ (a b m : ℕ) (Kth K : ℝ → ℝ → ℝ),
    ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
    ∀ c d : ℝ, 0 < c → 0 < d →
    ∃ (P : DynBrooks.Program) (aw : ℕ) (c₁ c₂ : ℝ) (η : ℕ → ℕ → ℝ),
      0 < c₁ ∧ c₁ ≤ c₂ ∧
      (∀ n Δ : ℕ, 2 ≤ n → 1 ≤ Δ →
        c₁ * Real.logb 2 n ^ 2 / Δ ≤ η n Δ ∧ η n Δ ≤ c₂ * Real.logb 2 n ^ 2 / Δ) ∧
      ∀ n Δ : ℕ, 2 ≤ n → Kth c d * (1 / ε) ^ a * Real.logb 2 n ^ b ≤ (Δ : ℝ) →
      ∀ σ : List (DynBrooks.Update n), IsLegalSeq Δ σ → (σ.length : ℝ) ≤ (n : ℝ) ^ d →
        DynBrooks.coinMeasure (wordSize aw n)
          {ω | ¬ (
            -- preprocessing completes
            (stateAt P ω [n, min Δ (2 * n)] σ 0).isSome ∧
            -- worst-case update time poly(1/ε) log³ n
            (∀ t < σ.length, TimeLE (updateTime P ω [n, min Δ (2 * n)] σ t)
              (K c d * (1 / ε) ^ m * Real.logb 2 n ^ 3)) ∧
            -- Definition 4.1, Parts 1–3, after preprocessing and after every update
            (∀ t ≤ σ.length,
              IsSmoothACD ε cSp Δ (graphAt σ t) (decompAt P ω [n, min Δ (2 * n)] σ t)) ∧
            -- property 1: whenever ℓ(i) is set to Reg, z(C_i) ≥ ρ ≥ cρ ε² Δ
            (∀ t ≤ σ.length, ∀ i : ℕ,
              (decompAt P ω [n, min Δ (2 * n)] σ t).reg i = true →
              (decompBefore P ω [n, min Δ (2 * n)] σ t).reg i = false →
              cρ * ε ^ 2 * Δ ≤
                zC Δ (graphAt σ t) (clusterSet (decompAt P ω [n, min Δ (2 * n)] σ t) i)) ∧
            -- property 2: total recourse of Ã and Ẽ during one update
            (∀ t, 1 ≤ t → t ≤ σ.length →
              ((∑ v : Fin n,
                ((symmDiff ((decompAt P ω [n, min Δ (2 * n)] σ t).At v)
                    ((decompAt P ω [n, min Δ (2 * n)] σ (t - 1)).At v)).card +
                  (symmDiff ((decompAt P ω [n, min Δ (2 * n)] σ t).Et v)
                    ((decompAt P ω [n, min Δ (2 * n)] σ (t - 1)).Et v)).card) : ℕ) : ℝ) ≤
                K c d * (1 / ε) ^ m * Real.logb 2 n ^ 2) ∧
            -- property 3(a)
            (∀ τ' τ : ℕ, 1 ≤ τ' → τ' ≤ τ → τ ≤ σ.length →
              (partitionRecourse (decompAt P ω [n, min Δ (2 * n)] σ) τ' τ : ℝ) ≤
                2 + η n Δ * ((τ : ℝ) - τ')) ∧
            -- property 3(b)
            (∀ (v : Fin n) (τ' τ : ℕ), 1 ≤ τ' → τ' ≤ τ → τ ≤ σ.length →
              (∀ t ∈ Finset.Icc τ' τ, v ∉ (decompAt P ω [n, min Δ (2 * n)] σ t).B) →
              ((setRecourse (fun t => (decompAt P ω [n, min Δ (2 * n)] σ t).At v) τ' τ +
                  setRecourse (fun t => (decompAt P ω [n, min Δ (2 * n)] σ t).Et v) τ' τ : ℕ) : ℝ)
                ≤ 4 + η n Δ * ((τ : ℝ) - τ') +
                  (((Finset.Icc τ' τ).filter fun t => IsIncident σ t v).card : ℝ)) ∧
            -- property 3(c)
            (∀ (v : Fin n) (τ : ℕ), 1 ≤ τ → τ ≤ σ.length →
              (decompAt P ω [n, min Δ (2 * n)] σ τ).C v ≠
                (decompAt P ω [n, min Δ (2 * n)] σ (τ - 1)).C v →
              (τ : ℝ) + 1 / η n Δ ≤ σ.length →
              1 / η n Δ ≤ (((Finset.range (σ.length + 1)).filter fun t : ℕ =>
                |(t : ℝ) - τ| ≤ 1 / η n Δ ∧
                  v ∈ (decompAt P ω [n, min Δ (2 * n)] σ t).B).card : ℝ)))}
          ≤ ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end DynColorWC.Main
