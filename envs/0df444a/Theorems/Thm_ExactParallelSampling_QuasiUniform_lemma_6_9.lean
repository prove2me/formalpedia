-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_6_9
-- name    : ExactParallelSampling.QuasiUniform.lemma_6_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:52:05.258878+00:00
-- url     : https://prove2.me/theorems/312ea171-399c-4f2d-9bc3-12f407fb2653
-- title:
--   Lemma 6.9 — α-growth along non-terminal peels, including the second alternative α(S_j) > ℓ
-- statement:
--   Standing assumptions of §6: $I$ is an independence system with (A1) on a ground set $E$ of $n\ge n_0(\gamma)$ elements, $\gamma\in(0,1]$, $c_\gamma=48/\gamma$ and $\delta=n^{-1-\gamma}$.
--
--   Assume $G$, and let $i<j$ be non-terminal peels with $|S_i|\le2|S_j|$. Let $\beta=\alpha(S_i)|S_j|/|S_i|$ and $\ell=\lfloor\alpha(S_i)|M_i|/|S_i|\rfloor$. Then
--   $$\alpha(S_j)\ge\beta+\sqrt{\beta\log n/c_\gamma}\quad\text{or}\quad\alpha(S_j)>\ell .$$
--   In the second case, $\alpha(S_j)/|S_j|\ge2\alpha(S_i)/|S_i|$.
--
--   The Lean states this for every $M=M_i$, $S_i\subseteq M$ and $S_j\subseteq M\setminus S_i$ that satisfy what $G$ and non-terminality give (p. 34):
--   - $S_i$ and $S_j$ are dependent;
--   - $\varphi^{M}_{S_i}\ge1-\delta$;
--   - $\alpha(S)\le|S|/(100\log n)$ and $|S|\le n/4$ for $S\in\{S_i,S_j\}$;
--   - $|M\setminus S_i|\ge n/2$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §6: I an independence system on E, |E| = n, (A1) every singleton independent → SubsamplingSM.Offline.IsIndepSystem I (∅ ∈ I, downward closed; no exchange axiom) and ∀ x, I {x}; E a finite type with n = Fintype.card E; reason: the published predicate is exactly the definition of an independence system
--   - encoding: n ≥ n₀(γ), where n₀(γ) ≥ 2^{34/γ} also exceeds a sufficiently large absolute constant → ∃ n₀ (chosen after γ), ∀ ground sets with n ≥ n₀; reason: the source leaves the threshold unspecified beyond being sufficiently large, so it is an existential threshold depending only on γ
--   - generalization: assume the event G for a run of Iterate, and let i < j be non-terminal peels of it → any sets M, S_i ⊆ M, S_j ⊆ M ∖ S_i with S_i, S_j dependent, φ^M_{S_i} ≥ 1 − δ, α(S) ≤ |S|/(100 log n) and |S| ≤ n/4 for S ∈ {S_i, S_j}, |M ∖ S_i| ≥ n/2, |S_i| ≤ 2|S_j|; reason: p. 34 lists exactly these as consequences of G and non-terminality (S_j ⊆ M_j ⊆ M_i ∖ S_i; α ≤ α̂ ≤ |S|/(100 log n); |M_i| ≥ |M_i ∖ S_i| ≥ n/2), so the peels of every run on G satisfy them and the statement specializes to the source's
--   - encoding: log n → Real.logb 2 n; reason: logarithms are base 2 (p. 12)
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 6.9, p. 34; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_IndepSystems

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 6.9 (α-growth)**, Shen, Li, Shi and Li (2026), p. 34. Standing assumptions of §6
(independence system with (A1), `|E| = n ≥ n₀(γ)`, `c_γ = 48/γ`, `δ = n^{−1−γ}`). Assume `G` and
let `i < j` be non-terminal peels with `|S_i| ≤ 2|S_j|`. Let `β = α(S_i)|S_j|/|S_i|` and
`ℓ = ⌊α(S_i)|M_i|/|S_i|⌋`. Then `α(S_j) ≥ β + √(β log n / c_γ)` or `α(S_j) > ℓ`; in the second case
`α(S_j)/|S_j| ≥ 2 α(S_i)/|S_i|`.
Stated for every `M = M_i`, `S_i ⊆ M` and `S_j ⊆ M ∖ S_i` with the properties that `G` and
non-terminality give: `S_i, S_j` dependent, `φ^M_{S_i} ≥ 1 − δ`, `α(S) ≤ |S|/(100 log n)` and
`|S| ≤ n/4` for `S ∈ {S_i, S_j}`, and `|M ∖ S_i| ≥ n/2`. -/
theorem lemma_6_9 : ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∃ n0 : ℕ,
    ∀ {E : Type} [Fintype E], n0 ≤ Fintype.card E →
    ∀ I : Finset E → Prop, SubsamplingSM.Offline.IsIndepSystem I → (∀ x, I {x}) →
    ∀ M Si Sj : Finset E, Si ⊆ M → Sj ⊆ M \ Si → ¬ I Si → ¬ I Sj →
      1 - deltaP (Fintype.card E) γ ≤ phi I M Si →
      (alphaVal I Si : ℝ) ≤ (Si.card : ℝ) / (100 * Real.logb 2 (Fintype.card E)) →
      (alphaVal I Sj : ℝ) ≤ (Sj.card : ℝ) / (100 * Real.logb 2 (Fintype.card E)) →
      (Si.card : ℝ) ≤ (Fintype.card E : ℝ) / 4 → (Sj.card : ℝ) ≤ (Fintype.card E : ℝ) / 4 →
      (Fintype.card E : ℝ) / 2 ≤ ((M \ Si).card : ℝ) →
      Si.card ≤ 2 * Sj.card →
      let β : ℝ := (alphaVal I Si : ℝ) * Sj.card / Si.card
      let ℓ : ℕ := ⌊(alphaVal I Si : ℝ) * M.card / Si.card⌋₊
      (β + Real.sqrt (β * Real.logb 2 (Fintype.card E) / cgam γ) ≤ (alphaVal I Sj : ℝ) ∨
          ℓ < alphaVal I Sj) ∧
        (ℓ < alphaVal I Sj →
          2 * (alphaVal I Si : ℝ) / Si.card ≤ (alphaVal I Sj : ℝ) / Sj.card) := by sorry

end ExactParallelSampling.QuasiUniform
