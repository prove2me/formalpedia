-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_Supplement_theorem_1_7
-- name    : BourgainUnion.Euclidean.Supplement.theorem_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:38:56.084284+00:00
-- url     : https://prove2.me/theorems/daa843e0-effd-4bdc-a790-0c79f0fb76bc
-- title:
--   Theorem 1.7 — unions of sets with constant distortion
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $(X,d)$ be a metric space with $X=U_1\cup\dots\cup U_k$, $k\ge1$, where each $U_i$ embeds into $\ell_2$ with distortion $C_i\ge1$, and let $C_{\max}=\max_iC_i$. Then $X$ embeds into $\ell_2$ with distortion
--   $$D\le C\cdot C_{\max}\,k^{\eta(C_{\max})}\log(k+1).$$
--   Here, for $c\ge1$, $\eta(c)$ is the root $\eta\ge c-1$ of $((1+\eta)^2-c^2)((1+\eta/2)^2-2)=\pi c^2/2$ (Section 7). Moreover, for every $c\ge1$ this root exists, and
--   $$\eta(c)\le c-1+\frac{\pi}{c},\qquad \eta(1)=\eta_0,$$
--   where $\eta_0$ is the exponent of equation (16).
--
--   Differences from the source:
--   - encoding: distortion O(C_max k^{η(C_max)} log k) → one positive constant C, chosen before X, k, the cover and the C_i, with D ≤ C·C_max·k^{η(C_max)}·log(k+1), for k ≥ 1; reason: the constant of the proof (3√2 times Theorem 2.7's) is absolute; log(k+1) as in the base mission
--   - encoding: each U_i embeds in ℓ2 with distortion C_i ≥ 1 → the published Embeds (C i) on the subspace U i, with no separate hypothesis 1 ≤ C i; reason: Embeds includes 1 ≤ C i, so a separate hypothesis would be redundant
--   - encoding: C_max = max_i C_i → the real supremum ⨆ i, C i over Fin k with k ≥ 1; reason: a finite nonempty index set, so the supremum is the attained maximum
--   - generalization: η(c) defined as the unique root η ≥ c − 1 (existence asserted in the text of §7, p. 27) → an extra conclusion: for every c ≥ 1, η(c) ≥ c − 1 and η(c) solves its equation; reason: it makes the infimum definition of η(c) non-vacuous; dropping the conjunct gives the source statement
--   - encoding: η(1) = η₀ → etaC 1 = eta0 against the published eta0 of equation (16); reason: the base mission's definition of η₀
--   - encoding: a finite indexed cover X = U1 ∪ … ∪ Uk → U : Fin k → Set X with pointwise coverage, k ≥ 1; reason: zero-based indexing only; overlapping and empty members are permitted, as in the base goal
--   - encoding: real ℓ₂ → square-summable real sequences H2 = lp (fun _ : ℕ => ℝ) 2; reason: H2 is real ℓ₂, the published target of the base mission
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 4, §1.2, Theorem 1.7 (η(c): §7, p. 27; η₀: equation (16))

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel
import Definitions.Def_BourgainUnion_Euclidean_Exponents
import Definitions.Def_BourgainUnion_Euclidean_Supplement_EtaModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

open BourgainUnion.Euclidean

/-- Theorem 1.7, p. 4, with `η(c)` of §7, p. 27: `η(c)` is a root `≥ c − 1` of its equation,
`η(c) ≤ c − 1 + π/c`, `η(1) = η₀`, and the distortion bound with one universal constant. -/
theorem theorem_1_7 :
    (∀ c : ℝ, 1 ≤ c → c - 1 ≤ etaC c ∧
      ((1 + etaC c)^2 - c^2) * ((1 + etaC c / 2)^2 - 2) = Real.pi * c^2 / 2) ∧
    (∀ c : ℝ, 1 ≤ c → etaC c ≤ c - 1 + Real.pi / c) ∧
    etaC 1 = eta0 ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type) [MetricSpace X] (k : ℕ), 1 ≤ k →
        ∀ (U : Fin k → Set X) (Cd : Fin k → ℝ), Covers U →
          (∀ i, Embeds (X := (U i)) (Cd i)) →
          ∃ D : ℝ, D ≤ C * (⨆ i, Cd i) * (k:ℝ)^(etaC (⨆ i, Cd i)) * Real.log (k+1) ∧
            Embeds (X := X) D := by sorry

end BourgainUnion.Euclidean.Supplement
