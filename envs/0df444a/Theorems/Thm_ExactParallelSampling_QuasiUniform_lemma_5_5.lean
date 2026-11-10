-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_5_5
-- name    : ExactParallelSampling.QuasiUniform.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:50:52.916724+00:00
-- url     : https://prove2.me/theorems/3af5e7bf-3ba5-403b-9adf-fe21041e789b
-- title:
--   Lemma 5.5 — adaptive moment recovery computes H, every weight and every circuit in 2 + ⌈log₂ max(1, ⌊log₂ h⌋)⌉ rounds
-- statement:
--   Let $\mu$ be quasi-uniform, $B$ independent, $x\notin B$ with $B+x$ dependent, $r=s_x$ and $h=|H|$. The adaptive procedure of steps 1–5 below computes $H$, every $w_A$, and hence every circuit of $B+x$. The procedure asks support-size queries $s(Z)$, $Z\subseteq B$, at a fixed pinning $z\in\prod_{b\in B}\Omega_b$, and reads them as $F(Z)=1/s(Z)-1/r$; it is not given $h$.
--
--   1. **Round 1.** $C_1=\{\emptyset\}\cup\{\{i\}:i\in B\}$. Query $G_{C_1}$, and let $T_1$ be a maximal subfamily with nonsingular Gram matrix, chosen greedily with $\emptyset$ first.
--   2. **Round $j\ge2$.** $C_j=T_{j-1}\cup\{S\cup S'\}\cup\{S\cup\{i\}\}$. Query $G_{C_j}$. If $\operatorname{rank}G_{C_j}=|T_{j-1}|$, stop with $T=T_{j-1}$; otherwise extend $T_{j-1}$ to a maximal nonsingular subfamily $T_j$ of $C_j$.
--   3. **At the stop.** Form $G_T$, $K_i=(F(B\setminus(S_a\cup S_b\cup\{i\})))_{a,b}$ and $M_i=G_T^{-1}K_i$.
--   4. **Splitting.** Split by the left kernels of $M_i$ and $M_i-I$, one coordinate $i\in B$ at a time.
--   5. **Output.** The label sets $A=\{i:\lambda_i=0\}$ of the surviving lines, with weights the diagonal of $E^{-\top}G_TE^{-1}$, where $E$ has as rows the line vectors normalized by $e(\emptyset)=1$.
--
--   **Rounds.** It uses at most $2+\lceil\log_2\max(1,\lfloor\log_2h\rfloor)\rceil$ rounds of support-size queries (and stops in round $\ge2$).
--
--   **Queries.** At most $(|B|+1)^2$ in the first round and at most $(h^2+h(|B|+1))^2$ in each later round.
--
--   **Output.** It outputs exactly $H$ with $w_A$ for each $A\in H$. The circuits of $B+x$ are the sets $A+x$, $A$ minimal in the output.
--
--   **Adaptivity.** It uses only the answers to its queries.
--
--   This holds for every admissible choice of the maximal nonsingular subfamilies and every product-support pinning $z$.
--
--   The final Gram matrix is nonsingular, its index family has h members, and every surviving labelled subspace is a line with the stated normalized vector.
--
--   Differences from the source:
--   - encoding: a distribution μ on Σ^E = ∏_{j∈E} Σ_j → a mass function p : (E → α) → ℝ with IsDist p, on a finite alphabet α containing every Σ_j; reason: assignments outside ∏ Σ_j get mass 0, which changes no probability, support, conditional law or independent set
--   - generalization: the maximal nonsingular subfamilies T_j "chosen greedily with ∅ first" (round 1) and T_j ⊇ T_{j−1} (later rounds) → any admissible selection rule sel (IsMaxNonsingularSelection B sel): a maximal nonsingular extension of the family already chosen, depending only on the entries of G_{C_j}; round 1 is sel applied to {∅}; reason: every greedy scan with ∅ first is such a rule, so the statement for all admissible rules contains the source's
--   - encoding: support-size queries s(Z) at a fixed pinning z ∈ ∏_{b∈B} Ω_b → ssQuery p x Z z for an arbitrary z with z_b ∈ Ω_b for b ∈ B (the theorem holds for every such z); reason: the source fixes an arbitrary such z
--   - encoding: step 4: successive splitting of the list ((ℚ^{h′}, ∅)) by ker_ℓ M_i and ker_ℓ(M_i − I), dropping zero subspaces → momLabelSpace A = ⋂_{i∈A} ker_ℓ M_i ∩ ⋂_{i∈B∖A} ker_ℓ(M_i − I), kept iff nonzero (momOut); reason: intersections commute and a zero subspace stays zero, so the final list consists of exactly these subspaces and labels
--   - encoding: Gaussian elimination over ℚ → subspaces of ℝ^T and real matrix inverses; reason: the matrices are rational and exact computation is free; kernels and inverses agree over ℚ and ℝ
--   - encoding: the number of rounds; the queries of a round → momStop (the stopping round J); the distinct sets B ∖ (S ∪ S′), S, S′ ∈ C_j (gramQueries), whose number is at most the number |C_j|² of entries of G_{C_j}; reason: each entry of G_{C_j} is one support-size query; repeated entries need not be asked twice
--   - encoding: "it does not need to know h" → the procedure's definition takes only B, r, the answers and sel; reason: structural
--   - generalization: "adaptive procedure" → an added conclusion: any answers that agree with the true ones on every queried set give the same stopping round, output family and weights; reason: this makes explicit that the procedure uses only the answers to its queries; dropping the conjunct gives the source statement
--   - encoding: Every subspace left after splitting is a line, normalized by e(∅)=1 (step 5) → the final family has h members and nonsingular Gram matrix; each surviving momLabelSpace has real dimension one and momLineVec belongs to it with its empty-set coordinate equal to one; reason: these are assertions about the constructed output, not assumptions that hide the validity of the inverse or normalization
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 5.5, p. 26–27; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_EfronStein
import Definitions.Def_ExactParallelSampling_QuasiUniform_MomentRecovery

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 5.5 (Moment recovery)**, Shen, Li, Shi and Li (2026), pp. 26–27. Let `μ` be
quasi-uniform, `B` independent, `x ∉ B` with `B + x` dependent, `r = s_x` and `h = |H|`. The adaptive
procedure of steps 1–5 (with support-size queries at a fixed pinning `z ∈ ∏_{b ∈ B} Ω_b`, and any
admissible choice of the maximal nonsingular subfamilies) computes `H`, every `w_A`, and hence every
circuit of `B + x`. It uses at most `2 + ⌈log₂ max(1, ⌊log₂ h⌋)⌉` rounds of support-size queries, at
most `(|B| + 1)²` in the first round and at most `(h² + h(|B| + 1))²` in each later round, and it
does not need to know `h`; its queries of each round, and its output, depend only on the answers
to its queries. -/
theorem lemma_5_5 {E α : Type*} [Fintype E] [Fintype α] (p : (E → α) → ℝ)
    (hp : IsQuasiUniform p) (B : Finset E) (x : E) (hB : IsIndep p B) (hx : x ∉ B)
    (hdep : ¬ IsIndep p (insert x B)) (z : E → α) (hz : ∀ b ∈ B, z b ∈ singleSupp p b)
    (sel : (Finset E → ℝ) → Finset (Finset E) → Finset (Finset E) → Finset (Finset E))
    (hsel : IsMaxNonsingularSelection B sel) :
    let r := s p x
    let Fv : Finset E → ℝ := momF r (fun Z => ssQuery p x Z z)
    let h := (esH p B x).card
    let J := momStop B Fv sel
    -- rounds
    2 ≤ J ∧ J ≤ 2 + ⌈Real.logb 2 ((max 1 ⌊Real.logb 2 (h : ℝ)⌋₊ : ℕ) : ℝ)⌉₊ ∧
    -- queries per round
    (gramQueries B (momC B Fv sel 1)).card ≤ (B.card + 1) ^ 2 ∧
    (∀ j, 2 ≤ j → j ≤ J →
      (gramQueries B (momC B Fv sel j)).card ≤ (h ^ 2 + h * (B.card + 1)) ^ 2) ∧
    -- output: `H`, every weight, every circuit
    (momFinalT B Fv sel).card = h ∧
    (gram B Fv (momFinalT B Fv sel)).det ≠ 0 ∧
    (∀ A ∈ momOut B Fv sel, Module.finrank ℝ (momLabelSpace B Fv sel A) = 1 ∧
      ∃ h0 : (∅ : Finset E) ∈ momFinalT B Fv sel,
        momLineVec B Fv sel A ∈ momLabelSpace B Fv sel A ∧
        momLineVec B Fv sel A ⟨∅, h0⟩ = 1) ∧
    momOut B Fv sel = esH p B x ∧
    (∀ A ∈ esH p B x, momWeight B Fv sel A = esWeight p B x A) ∧
    circuitsIn (IsIndep p) (insert x B) =
      ((momOut B Fv sel).filter (fun A => ∀ A' ∈ momOut B Fv sel, A' ⊆ A → A' = A)).image
        (insert x) ∧
    -- adaptivity: only the answers to its queries are used
    (∀ ss' : Finset E → ℕ,
      (∀ j, 1 ≤ j → j ≤ J → ∀ Z ∈ gramQueries B (momC B Fv sel j), ss' Z = ssQuery p x Z z) →
        momStop B (momF r ss') sel = J ∧ momOut B (momF r ss') sel = momOut B Fv sel ∧
          ∀ A, momWeight B (momF r ss') sel A = momWeight B Fv sel A) := by sorry

end ExactParallelSampling.QuasiUniform
