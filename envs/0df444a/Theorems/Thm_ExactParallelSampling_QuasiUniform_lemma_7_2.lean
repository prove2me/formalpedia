-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_7_2
-- name    : ExactParallelSampling.QuasiUniform.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:50:56.551128+00:00
-- url     : https://prove2.me/theorems/9bb2a788-ce92-4e46-846b-191c86462cfa
-- title:
--   Lemma 7.2 — moment recovery is a circuit recovery (A2) with ρ ≤ R_q; h < L_q; under divisibility h ≤ q − 1 and ρ ≤ R'_q
-- statement:
--   Let $q\ge2$ and let $\mu$ be a quasi-uniform distribution whose alphabet has at most $q$ symbols. Let $B$ be independent and $x\notin B$ with $B+x$ dependent. The procedure of Lemma 5.5 is a circuit recovery for $I=I(\mu)$ in the sense of (A2), with $\rho\le R_q=2+\lceil\log_2\log_2L_q\rceil$, $L_q=\mathrm{lcm}(1,\dots,q)$. That is:
--
--   - it computes exactly the family of all circuits contained in $B+x$, namely the sets $A+x$ for the minimal members $A$ of its output;
--   - it is deterministic, and its queries and output depend only on the answers to its queries;
--   - it stops in $\rho\le R_q$ rounds.
--
--   An instance $(B,x)$ uses at most $(|B|+1)^2$ support-size queries in its first round and at most $(h^2+h(|B|+1))^2$ in each later round, where $h<L_q$ is the number of nonzero Efron–Stein components of the conditional law of $X_x$ given $X_B$ (Lemma 5.1). If $s_T(x)$ divides $s_x$ for every $T\subseteq B$, then $h\le q-1$ and $\rho\le R'_q=2+\lceil\log_2\log_2q\rceil$.
--
--   Differences from the source:
--   - encoding: a distribution μ on Σ^E = ∏_{j∈E} Σ_j → a mass function p : (E → α) → ℝ with IsDist p, on a finite alphabet α containing every Σ_j; reason: assignments outside ∏ Σ_j get mass 0, which changes no probability, support, conditional law or independent set
--   - generalization: I = I(ν) restricted to the non-constant coordinates E′ of a distribution ν reached in line 3 of Algorithm 1 on [q]^n → any quasi-uniform μ on α^E with |α| ≤ q, and any B, x in E; reason: every ν reached by Algorithm 1 is a quasi-uniform law with alphabet of size ≤ q (Lemma 2.4), so this covers the source's instances
--   - encoding: ρ ≤ R_q, ρ ≤ R′_q → the stopping round J = momStop satisfies 2 ≤ J ≤ Rq q (resp. ≤ Rq' q); reason: J is the number of rounds of the procedure
--   - encoding: s_T(x) divides s_x → condSizeNat p T x ∣ s p x; reason: for quasi-uniform μ, condSizeNat equals the integer s_T(x) (Lemma 2.4(b))
--   - generalization: the maximal nonsingular subfamilies T_j "chosen greedily with ∅ first" (round 1) and T_j ⊇ T_{j−1} (later rounds) → any admissible selection rule sel (IsMaxNonsingularSelection B sel): a maximal nonsingular extension of the family already chosen, depending only on the entries of G_{C_j}; round 1 is sel applied to {∅}; reason: every greedy scan with ∅ first is such a rule, so the statement for all admissible rules contains the source's
--   - encoding: support-size queries s(Z) at a fixed pinning z ∈ ∏_{b∈B} Ω_b → ssQuery p x Z z for an arbitrary z with z_b ∈ Ω_b for b ∈ B (the theorem holds for every such z); reason: the source fixes an arbitrary such z
--   - encoding: step 4: successive splitting of the list ((ℚ^{h′}, ∅)) by ker_ℓ M_i and ker_ℓ(M_i − I), dropping zero subspaces → momLabelSpace A = ⋂_{i∈A} ker_ℓ M_i ∩ ⋂_{i∈B∖A} ker_ℓ(M_i − I), kept iff nonzero (momOut); reason: intersections commute and a zero subspace stays zero, so the final list consists of exactly these subspaces and labels
--   - encoding: Gaussian elimination over ℚ → subspaces of ℝ^T and real matrix inverses; reason: the matrices are rational and exact computation is free; kernels and inverses agree over ℚ and ℝ
--   - encoding: the number of rounds; the queries of a round → momStop (the stopping round J); the distinct sets B ∖ (S ∪ S′), S, S′ ∈ C_j (gramQueries), whose number is at most the number |C_j|² of entries of G_{C_j}; reason: each entry of G_{C_j} is one support-size query; repeated entries need not be asked twice
--   - encoding: "it does not need to know h" → the procedure's definition takes only B, r, the answers and sel; reason: structural
--   - generalization: "adaptive procedure" → an added conclusion: any answers that agree with the true ones on every queried set give the same stopping round, output family and weights; reason: this makes explicit that the procedure uses only the answers to its queries; dropping the conjunct gives the source statement
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 7.2, p. 37; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_EfronStein
import Definitions.Def_ExactParallelSampling_QuasiUniform_MomentRecovery

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 7.2 (Circuit recovery by moments)**, Shen, Li, Shi and Li (2026), p. 37. For a
quasi-uniform distribution with alphabet size at most `q ≥ 2`, the procedure of Lemma 5.5 is a
circuit recovery for `I` in the sense of (A2): for `B ∈ I`, `x ∉ B`, `B + x ∉ I` it computes the
family of all circuits contained in `B + x`, deterministically, with queries depending only on
earlier answers, in `ρ ≤ R_q` rounds. An instance `(B, x)` uses at most `(|B| + 1)²` support-size
queries in its first round and at most `(h² + h(|B| + 1))²` in each later round, where `h < L_q`.
If `s_T(x)` divides `s_x` for every `T ⊆ B`, then `h ≤ q − 1` and `ρ ≤ R'_q = 2 + ⌈log₂ log₂ q⌉`. -/
theorem lemma_7_2 (q : ℕ) (hq : 2 ≤ q) {E α : Type*} [Fintype E] [Fintype α]
    (hα : Fintype.card α ≤ q) (p : (E → α) → ℝ) (hp : IsQuasiUniform p) (B : Finset E) (x : E)
    (hB : IsIndep p B) (hx : x ∉ B) (hdep : ¬ IsIndep p (insert x B)) (z : E → α)
    (hz : ∀ b ∈ B, z b ∈ singleSupp p b)
    (sel : (Finset E → ℝ) → Finset (Finset E) → Finset (Finset E) → Finset (Finset E))
    (hsel : IsMaxNonsingularSelection B sel) :
    let r := s p x
    let Fv : Finset E → ℝ := momF r (fun Z => ssQuery p x Z z)
    let h := (esH p B x).card
    let J := momStop B Fv sel
    -- (A2): all circuits of `B + x`, exactly
    circuitsIn (IsIndep p) (insert x B) =
      ((momOut B Fv sel).filter (fun A => ∀ A' ∈ momOut B Fv sel, A' ⊆ A → A' = A)).image
        (insert x) ∧
    (∀ ss' : Finset E → ℕ,
      (∀ j, 1 ≤ j → j ≤ J → ∀ Z ∈ gramQueries B (momC B Fv sel j), ss' Z = ssQuery p x Z z) →
        momStop B (momF r ss') sel = J ∧ momOut B (momF r ss') sel = momOut B Fv sel ∧
          ∀ A, momWeight B (momF r ss') sel A = momWeight B Fv sel A) ∧
    -- rounds and queries
    2 ≤ J ∧ J ≤ Rq q ∧
    (gramQueries B (momC B Fv sel 1)).card ≤ (B.card + 1) ^ 2 ∧
    (∀ j, 2 ≤ j → j ≤ J →
      (gramQueries B (momC B Fv sel j)).card ≤ (h ^ 2 + h * (B.card + 1)) ^ 2) ∧
    h < Lq q ∧
    -- divisibility
    ((∀ T ⊆ B, condSizeNat p T x ∣ s p x) → h ≤ q - 1 ∧ J ≤ Rq' q) := by sorry

end ExactParallelSampling.QuasiUniform
