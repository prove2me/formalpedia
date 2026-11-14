-- Prove2me | Theorems.Thm_BosonicLearn_lemma_12
-- name    : BosonicLearn.lemma_12
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T07:40:21.727367+00:00
-- url     : https://prove2.me/theorems/487aeb04-f768-45ca-8696-f7cb670b3058
-- title:
--   Lemma 12 — $\|X_2-X_1\|_{\mathrm{tr}}\ge an$ forces $\|\rho_{R_{X_2}}-\rho_{R_{X_1}}\|_{\mathrm{tr}}\ge C_a\xi\sqrt{n\nu}$
-- statement:
--   Assume $1/n\le\nu\le1$. For every $a>0$ there are constants $C_a,\alpha_a>0$ such that, whenever $\xi\le\alpha_a/\sqrt{n\nu}$ and $X_1,X_2\in G_{\mathrm{supp}}$ satisfy $\|X_2-X_1\|_{\mathrm{tr}}\ge an$,
--
--   $$\big\|\rho_{R_{X_2}}-\rho_{R_{X_1}}\big\|_{\mathrm{tr}}\ge C_a\,\xi\sqrt{n\nu},$$
--
--   where $\rho_R=\det(I-R)\Gamma(R)$ and $R_X=r(I+\xi X)$. It converts trace-distance accuracy on the states into accuracy on the parameter $X$.
--
--   Differences from the source:
--   - encoding: ‖·‖_tr of Fock operators; ξ ∈ (0, 1/32) standing (§5.1) → traceSize (full trace norm, no ½); hypotheses n ≥ 1, ξ ∈ (0, 1/32); reason: the paper's trace norm and standing assumptions
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 12, Eqs. (103)–(104), p. 40

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_Gsupp
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open scoped ENNReal

namespace BosonicLearn

/-- **Lemma 12 (Trace distance bound via fugacity matrix).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 12, Eqs. (103)–(104), p. 40: "Assume 1/n ≤ ν ≤ 1. For every a > 0, there exist constants C_a > 0,
α_a > 0 such that, whenever ξ ≤ α_a/√(nν), if X_1, X_2 ∈ G_supp and ‖X_2 − X_1‖_tr ≥ an. Then,
‖ρ_{R_{X_2}} − ρ_{R_{X_1}}‖_tr ≥ C_a ξ √(nν)."

For every `a > 0` there are `C_a, α_a > 0` such that for all `n ≥ 1`, `ν ∈ [1/n, 1]`, `ξ ∈ (0, 1/32)` with
`ξ ≤ α_a/√(nν)`, and all `X₁, X₂ ∈ G_supp` with `‖X₂ − X₁‖_tr ≥ an`, the passive states `ρ_{R_X} = det(I − R_X)Γ(R_X)`,
`R_X = r(I + ξX)`, satisfy `‖ρ_{R_{X_2}} − ρ_{R_{X_1}}‖_tr ≥ C_a ξ √(nν)`.

**Formalization Note.** `‖·‖_tr` on Fock operators is the full trace norm `traceSize` (no factor ½). `ξ < 1/32` is the
standing assumption of §5.1 (p. 30), which keeps `R_X ≺ I`. -/
theorem lemma_12 :
    ∀ a : ℝ, 0 < a → ∃ Ca : ℝ, 0 < Ca ∧ ∃ αa : ℝ, 0 < αa ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 →
      ∀ ξ : ℝ, 0 < ξ → ξ < 1 / 32 → ξ ≤ αa / Real.sqrt (n * ν) →
      ∀ X₁ ∈ Gsupp n, ∀ X₂ ∈ Gsupp n,
        a * n ≤ WHMultiplicativity.schattenNorm 1 ((X₂ - X₁ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) →
        ENNReal.ofReal (Ca * ξ * Real.sqrt (n * ν)) ≤
          traceSize (fugacityCoeff (fugacityFamily ν ξ X₂) - fugacityCoeff (fugacityFamily ν ξ X₁)) := by sorry

end BosonicLearn
