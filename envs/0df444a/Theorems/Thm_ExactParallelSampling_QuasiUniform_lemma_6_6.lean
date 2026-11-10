-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_6_6
-- name    : ExactParallelSampling.QuasiUniform.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:51:58.672459+00:00
-- url     : https://prove2.me/theorems/c5444b17-8441-4670-b868-870d6d8a8657
-- title:
--   Lemma 6.6 — GreedyOpt returns, with probability ≥ 1 − 2^{−n}, a dependent S with φ^M_S ≥ 1 − δ and p_x(S) ≥ ε/2
-- statement:
--   Standing assumptions of §6: $I$ is an independence system on a ground set $E$ of $n\ge n_0(\gamma)$ elements, every singleton is independent (A1), $\gamma\in(0,1]$, $\delta=n^{-1-\gamma}$, $\varepsilon=\delta/(2n)$ and $N=\lceil1280n^{4+\gamma}\rceil$.
--
--   Let $M\subseteq E$ be dependent. GreedyOpt$(M)$ uses $1+\rho$ rounds: one with at most $N|M|\le1281n^{5+\gamma}$ independence queries, and $\rho$ rounds in which it runs $N$ instances of Rec in parallel. With probability at least $1-2^{-n}$ over its $N$ independent uniformly random orders of $M$, the returned set $S$ is dependent and satisfies $\varphi^M_S\ge1-\delta$ and $p_x(S)\ge\varepsilon/2=n^{-2-\gamma}/4$ for every $x\in S$. This holds for every linear order of $E$, which fixes "the first such $x$" in line 7.
--
--   The formal statement includes the concrete oracle execution: for every tuple of sampled orders and every correct recovery oracle it halts with greedyOpt as output, uses the two stated phases, and calls Rec only on its valid domain.
--
--   Differences from the source:
--   - encoding: standing assumptions of §6: I an independence system on E, |E| = n, (A1) every singleton independent → SubsamplingSM.Offline.IsIndepSystem I (∅ ∈ I, downward closed; no exchange axiom) and ∀ x, I {x}; E a finite type with n = Fintype.card E; reason: the published predicate is exactly the definition of an independence system
--   - encoding: n ≥ n₀(γ), where n₀(γ) ≥ 2^{34/γ} also exceeds a sufficiently large absolute constant → ∃ n₀ (chosen after γ), ∀ ground sets with n ≥ n₀; reason: the source leaves the threshold unspecified beyond being sufficiently large, so it is an existential threshold depending only on γ
--   - encoding: (A2): Rec computes every circuit of B+x in at most ρ rounds → for every correct recAns and every tuple of orders, greedyProtocol calls recover only at (A2) inputs and its output equals greedyOpt; reason: the concrete protocol reads prefix answers first, chooses recovery inputs from those answers, then computes the output from the recovered families
--   - encoding: GreedyOpt uses 1+ρ rounds, with at most N|M| independence queries then N parallel Rec instances → greedyProtocol takes exactly two transcript steps, with charged cost 1+ρ; the first batch has at most N|M| independence queries and no Rec calls, the second at most N Rec calls and no independence queries; reason: the second transcript step represents the whole parallel recovery phase of at most ρ rounds; duplicate queries may be shared
--   - encoding: "remove the first such x" → the least such x in the linear order of E; the theorem holds for every linear order; reason: the source does not fix the order
--   - encoding: N independent uniformly random orders of M → the uniform distribution on Fin N → Order M; reason: independent uniform coordinates form the uniform distribution on the product
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 6.6, p. 32; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_IndepSystems

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 6.6**, Shen, Li, Shi and Li (2026), p. 32. Standing assumptions of §6: `I` an
independence system on `E`, `|E| = n ≥ n₀(γ)`, every singleton independent (A1), `δ = n^{−1−γ}`,
`ε = δ/(2n)`, `N = ⌈1280 n^{4+γ}⌉`. Let `M ⊆ E` be dependent. GreedyOpt(M) uses `1 + ρ` rounds: one
with at most `N|M| ≤ 1281 n^{5+γ}` independence queries, and `ρ` rounds in which it runs `N`
instances of `Rec` in parallel. With probability at least `1 − 2^{−n}` (over its `N` independent
uniformly random orders of `M`), the returned set `S` is dependent and satisfies `φ^M_S ≥ 1 − δ`
and `p_x(S) ≥ ε/2 = n^{−2−γ}/4` for every `x ∈ S`. -/
theorem lemma_6_6 : ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∃ n0 : ℕ,
    ∀ {E : Type} [Fintype E] [LinearOrder E], n0 ≤ Fintype.card E →
    ∀ I : Finset E → Prop, SubsamplingSM.Offline.IsIndepSystem I → (∀ x, I {x}) →
    ∀ M : Finset E, ¬ I M →
      (∀ ρ : ℕ, ∀ recAns, IsCircuitRecovery I recAns →
        ∀ π : Fin (Nord (Fintype.card E) γ) → Order M, ∀ ω : Tape,
          let P := greedyProtocol (Fintype.card E) γ π
          let ans := indepOracle I recAns
          P.rounds ans ω = 2 ∧ iterRounds P ρ ans ω = ((1 + ρ : ℕ) : ℕ∞) ∧
          P.output ans ω = some (greedyOpt I (Fintype.card E) γ π) ∧
          RecoveryCallsValid P I ans ω ∧
          numIndep (P.batchAt ans ω 0) ≤ Nord (Fintype.card E) γ * M.card ∧
          numRec (P.batchAt ans ω 0) = 0 ∧ numIndep (P.batchAt ans ω 1) = 0 ∧
          numRec (P.batchAt ans ω 1) ≤ Nord (Fintype.card E) γ) ∧
      (greedyOptQueries (Fintype.card E) γ M : ℝ) ≤ 1281 * (Fintype.card E : ℝ) ^ (5 + γ) ∧
      epsP (Fintype.card E) γ / 2 = (Fintype.card E : ℝ) ^ (-2 - γ) / 4 ∧
      1 - (2 : ℝ) ^ (-(Fintype.card E : ℝ)) ≤
        uprob (Fin (Nord (Fintype.card E) γ) → Order M) (fun π =>
          ¬ I (greedyOpt I (Fintype.card E) γ π) ∧
          1 - deltaP (Fintype.card E) γ ≤ phi I M (greedyOpt I (Fintype.card E) γ π) ∧
          ∀ x ∈ greedyOpt I (Fintype.card E) γ π,
            epsP (Fintype.card E) γ / 2 ≤ essProb I (greedyOpt I (Fintype.card E) γ π) x) := by sorry

end ExactParallelSampling.QuasiUniform
