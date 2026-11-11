-- Prove2me | Theorems.Thm_DynColorWC_Main_theorem_3
-- name    : DynColorWC.Main.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:48:36.904734+00:00
-- url     : https://prove2.me/theorems/30aadac1-1df5-4561-a5b2-8ad5afd0dc56
-- title:
--   Theorem 3 — inlier/outlier labels atop the decomposition with properties 1–4, in poly(1/ε) log³ n worst-case time w.h.p.
-- statement:
--   Let $V_{sp},C_1,C_2,\dots$ be the vertex partition maintained by Theorem 2 and $\rho=\Theta(\varepsilon^2\Delta)$ as in Theorem 2(1). There is a dynamic algorithm that maintains vertex labels $\ell':V\to\{\mathrm{In},\mathrm{Out}\}$ and the sets $\mathrm{inliers}(C)$, $\mathrm{outliers}(C)$ for every $C_i$, such that
--   1. every $v$ with $\ell'(v)=\mathrm{In}$ has $C(v)\ne\perp$, $\ell(C(v))=\mathrm{Reg}$ and $\tilde z(v)\le1000\,z(C(v))+O(1)$;
--   2. every regular almost-clique $C$ with $|\mathrm{outliers}(C)|>\Delta/4$ has $z(C)>\Theta(\varepsilon^6\Delta)$;
--   3. when a vertex $v$ changes label, $\tilde z(v)\le O(z(C)+1)$;
--   4. for all times $\tau_1\le\tau_2$ and $\log\log n+O_\varepsilon(1)\le i\le\lfloor\log\Delta\rfloor$, during updates $[\tau_1,\tau_2]$ there are at most $O_\varepsilon\big(1+(\tau_2-\tau_1+1)2^{-i}\log^3n\big)$ changes over all sets $\mathrm{inliers}(C)$ and $\mathrm{outliers}(C)$ at a time when $z(C)\in[2^i,2^{i+1}]$;
--
--   and its worst-case update time is $\mathrm{poly}(1/\varepsilon)\log^3n$ w.h.p.
--
--   In Lean: one program maintains the decomposition with every guarantee of Theorem 2 (same quantifiers) and the labels, all inside one event of probability at least $1-n^{-c}$.
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
--   - encoding: 'Let V_sp, C_1, … be the vertex-partition maintained by Theorem 2 … There is a dynamic algorithm that maintains vertex labels ℓ′' → one program maintains Theorem 2's decomposition with all of Theorem 2's guarantees (same quantifiers and constants) and the labels ℓ′ (record tag 7; initially every label is Out), in one event; reason: the paper runs the labelling atop Theorem 2's algorithm (§4.6); the combination is what is used in §5
--   - encoding: O(1) (property 1), Θ(ε⁶Δ) (property 2), O(z(C) + 1) (property 3), O_ε(1) and O_ε(·) (property 4) → absolute K₁, c₆ > 0, K₃ fixed before ε; Kᵢ and Kc chosen with the program, after ε, c, d (they may depend on ε, c, d); reason: O(·) and Θ(·) are absolute; O_ε may depend on ε, and the count bound is a high-probability statement
--   - reading: (3) when a vertex v changes label, z̃(v) ≤ O(z(C) + 1) → at every time t with ℓ′_t(v) ≠ ℓ′ before t (initially Out), z̃(v) and z(C) are taken in G_t with C the cluster of v at t (∅ if unclustered, where Lean's z(∅) = Δ); reason: C is the cluster of v when the label changes
--   - reading: (4) changes over all sets inliers(C) and outliers(C) at a time when z(C) ∈ [2^i, 2^{i+1}], for log(log n) + O_ε(1) ≤ i ≤ ⌊log Δ⌋ → Σ_{t ∈ [τ₁, τ₂]} Σ_j (|inliers_t(C_j) ⊕ inliers_{t−1}(C_j)| + |outliers_t(C_j) ⊕ outliers_{t−1}(C_j)|) over cluster ids j with C_j nonempty after update t and 2^i ≤ z_t(C_j) ≤ 2^{i+1}; i natural with log₂ log₂ n + Kᵢ ≤ i ≤ ⌊log₂ Δ⌋; reason: a change is a vertex entering or leaving one of these sets at an update; z(C) is defined only for nonempty C
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Theorem 3, p. 18 (PDF 20); restated p. 40 (PDF 42)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynColorWC_Main_Model
import Definitions.Def_DynColorWC_Main_AlmostClique
import Definitions.Def_DynColorWC_Main_Decomposition

namespace DynColorWC.Main

open Classical in
/-- **Theorem 3** (Flin and Ghaffari (2026), STOC 2027 submission, sha256 93ebb2ff…3154300e3,
p. 18 (PDF 20); restated p. 40 (PDF 42)). Let `V_sp, C_1, C_2, …` be the vertex partition maintained
by Theorem 2, and `ρ = Θ(ε²Δ)` the value of Theorem 2(1). There is a dynamic algorithm that maintains
vertex labels `ℓ′ : V → {In, Out}` and the sets `inliers(C) = {v ∈ C : ℓ′(v) = In}` and
`outliers(C) = {v ∈ C : ℓ′(v) = Out}` for every set `C_i` of the partition, such that
1. every `v` with `ℓ′(v) = In` has `C(v) ≠ ⊥`, `ℓ(C(v)) = Reg`, and `z̃(v) ≤ 1000·z(C(v)) + O(1)`;
2. every regular almost-clique `C` with `|outliers(C)| > Δ/4` has `z(C) > Θ(ε⁶Δ)`;
3. when a vertex `v` changes label, `z̃(v) ≤ O(z(C) + 1)`;
4. for all times `τ₁ ≤ τ₂` and `log(log n) + O_ε(1) ≤ i ≤ ⌊log Δ⌋`, during updates `[τ₁, τ₂]` there are
   at most `O_ε(1 + (τ₂ − τ₁ + 1) 2^{−i} log³ n)` changes over all sets `inliers(C)` and
   `outliers(C)` at a time when `z(C) ∈ [2^i, 2^{i+1}]`;
and worst-case update time `poly(1/ε) log³ n` w.h.p.

Formal reading. One program maintains both the decomposition of Theorem 2, with **all** of
Theorem 2's guarantees (same quantifiers and constants as in `theorem_2`), and the labels `ℓ′`
(record tag 7 of `decompAt`; initially every vertex is `Out`), inside one event of measure at least
`1 − n^{-c}`. "W.h.p." is read as in §3 (p. 13) and in `theorem_2`: for every `ε` and all `c, d > 0`
there is a program (it may depend on `ε, c, d`, not on `n`, `Δ` or the sequence). The `O(1)` constants
`K₁`, `K₃` and the constant `c₆` of `Θ(ε⁶Δ)` are absolute (fixed before `ε`); the `O_ε(1)` in the
range of `i` is `Kᵢ`, fixed with the program; the `O_ε(·)` constant `Kc` may depend on `ε`, `c` and
`d`. In 3, `C` is the cluster of `v` after the change (and a change
during preprocessing is a change from the initial label `Out`). In 4, a change is a vertex entering or
leaving `inliers(C_j)` or `outliers(C_j)` at an update `t ∈ [τ₁, τ₂]`, counted when `C_j` is nonempty
after update `t` and `z(C_j) ∈ [2^i, 2^{i+1}]` then. Logarithms are base 2. -/
theorem theorem_3 :
    ∃ (cSp cρ K₁ K₃ c₆ : ℝ), 0 < cSp ∧ 0 < cρ ∧ 0 < c₆ ∧
    ∃ (a b m : ℕ) (Kth K : ℝ → ℝ → ℝ),
    ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
    ∀ c d : ℝ, 0 < c → 0 < d →
    ∃ (P : DynBrooks.Program) (aw : ℕ) (c₁ c₂ Kᵢ Kc : ℝ) (η : ℕ → ℕ → ℝ),
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
                  v ∈ (decompAt P ω [n, min Δ (2 * n)] σ t).B).card : ℝ)) ∧
            -- Theorem 3, property 1
            (∀ t ≤ σ.length, ∀ v : Fin n,
              (decompAt P ω [n, min Δ (2 * n)] σ t).inl v = true →
              ∃ i : ℕ, (decompAt P ω [n, min Δ (2 * n)] σ t).C v = some i ∧
                (decompAt P ω [n, min Δ (2 * n)] σ t).reg i = true ∧
                zTilde Δ (graphAt σ t) (clusterSet (decompAt P ω [n, min Δ (2 * n)] σ t) i) v ≤
                  1000 * zC Δ (graphAt σ t)
                    (clusterSet (decompAt P ω [n, min Δ (2 * n)] σ t) i) + K₁) ∧
            -- Theorem 3, property 2
            (∀ t ≤ σ.length, ∀ i : ℕ,
              (decompAt P ω [n, min Δ (2 * n)] σ t).reg i = true →
              (Δ : ℝ) / 4 < ((outliers (decompAt P ω [n, min Δ (2 * n)] σ t) i).card : ℝ) →
              c₆ * ε ^ 6 * Δ <
                zC Δ (graphAt σ t) (clusterSet (decompAt P ω [n, min Δ (2 * n)] σ t) i)) ∧
            -- Theorem 3, property 3
            (∀ t ≤ σ.length, ∀ v : Fin n,
              (decompAt P ω [n, min Δ (2 * n)] σ t).inl v ≠
                (decompBefore P ω [n, min Δ (2 * n)] σ t).inl v →
              zTilde Δ (graphAt σ t) (clusterOf (decompAt P ω [n, min Δ (2 * n)] σ t) v) v ≤
                K₃ * (zC Δ (graphAt σ t)
                  (clusterOf (decompAt P ω [n, min Δ (2 * n)] σ t) v) + 1)) ∧
            -- Theorem 3, property 4
            (∀ (τ₁ τ₂ i : ℕ), 1 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ σ.length →
              Real.logb 2 (Real.logb 2 n) + Kᵢ ≤ (i : ℝ) → i ≤ Nat.log 2 Δ →
              ((∑ t ∈ Finset.Icc τ₁ τ₂,
                  ∑ j ∈ clusterIds (decompAt P ω [n, min Δ (2 * n)] σ t)
                      (decompAt P ω [n, min Δ (2 * n)] σ (t - 1)),
                    if (clusterSet (decompAt P ω [n, min Δ (2 * n)] σ t) j).Nonempty ∧
                        (2 : ℝ) ^ i ≤ zC Δ (graphAt σ t)
                          (clusterSet (decompAt P ω [n, min Δ (2 * n)] σ t) j) ∧
                        zC Δ (graphAt σ t)
                          (clusterSet (decompAt P ω [n, min Δ (2 * n)] σ t) j) ≤ (2 : ℝ) ^ (i + 1)
                    then (symmDiff (inliers (decompAt P ω [n, min Δ (2 * n)] σ t) j)
                            (inliers (decompAt P ω [n, min Δ (2 * n)] σ (t - 1)) j)).card +
                          (symmDiff (outliers (decompAt P ω [n, min Δ (2 * n)] σ t) j)
                            (outliers (decompAt P ω [n, min Δ (2 * n)] σ (t - 1)) j)).card
                    else 0 : ℕ) : ℝ) ≤
                Kc * (1 + ((τ₂ : ℝ) - τ₁ + 1) * (2 : ℝ) ^ (-(i : ℝ)) * Real.logb 2 n ^ 3)))}
          ≤ ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end DynColorWC.Main
