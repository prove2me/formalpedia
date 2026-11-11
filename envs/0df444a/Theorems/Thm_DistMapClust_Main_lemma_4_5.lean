-- Prove2me | Theorems.Thm_DistMapClust_Main_lemma_4_5
-- name    : DistMapClust.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:05:58.000067+00:00
-- url     : https://prove2.me/theorems/ebd81318-d818-4e50-aa93-bdf61f7bc14b
-- title:
--   Lemma 4.5 — every selection's count is dominated by an ε-nice count of cost ≤ (1 + ε) times and entries ≤ (nd/ε)^4
-- statement:
--   Let $I=(P,U,W,f')$ be an $\varepsilon$-nice instance of Row-Wise Ordered Norm Mapping Selection, $\varepsilon>0$ sufficiently small, with values $u(p,\ell)_i=(1+\varepsilon)^{v(p,\ell)_i}a_i$, and let $\sigma$ be a mapping selection. Then there is an $\varepsilon$-nice count $c:[d]\times[0,b]\to\mathbb N$ with
--   $$\mathrm{cost}(c,i)\le(1+\varepsilon)\,\mathrm{cost}(c_\sigma,i)\ \ (i\in[d]),\qquad c\ge c_\sigma,\qquad c(i,j)\le(nd/\varepsilon)^4 .$$
--   It shows that near-optimal selections can be guessed through counts whose entries drop exponentially in the cost class, which is what makes the dynamic program of §4.2–4.3 polynomial.
--
--   **Formalization Note.** A count is `Fin d → ℕ → ℕ`, used on $j\le b$; $\varepsilon_0$ is universal.
--
--   Differences from the source:
--   - reading: Definition 4.4: interval(c, i, j) = [Σ_{j′=j+1}^b c(i, j), Σ_{j′=j}^b c(i, j))_R → the summand is c(i, j′); reason: obvious typo: with the printed summand the consistency cost(c_σ, i) = ord_{w_i}(…) claimed on p. 48 fails (INSIGHTS I2)
--   - reading: §4: 'We always assume ε > 0 to be sufficiently small' → there is a universal ε₀ > 0 such that the statement holds for every ε ∈ (0, ε₀); reason: the standing assumption of §4 (p. 46), with the threshold independent of the instance
--   - reading: v(p, ℓ) with u(p, ℓ)_i = (1 + ε)^{v(p,ℓ)_i} a_i, under the standing assumption 'we assume that u(p, ℓ)_i is always different from ∞' (p. 47) → hypothesis NiceRep ε a v: a ≥ 0 and every value equals ofReal((1 + ε)^{v p ℓ i} · a i) with v p ℓ i ∈ [b/2, b]; the statement is for every such (a, v); reason: v is defined only for finite values; a ≥ 0 because values are nonnegative reals; when a_i > 0 the exponents are unique
--   - encoding: [0, b] the integers 0, …, b; |[x−1, x)_R ∩ [lo, hi)_R| → j ≤ b; max(0, min(x, hi) − max(x − 1, lo)) with x − 1 the 0-based index; reason: Lean convention; same values
--   - encoding: index sets [k], [d], [ψ], [n] (1-based) → Fin k, Fin d, Fin ψ, Fin n (0-based); P an injective family Fin n → α; reason: Lean convention; same instances
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 48, Lemma 4.5

import Mathlib
import Definitions.Def_DistMapClust_Main_Selection

namespace DistMapClust.Main

/-- Lemma 4.5 (p. 48), for `ε` sufficiently small (a universal `ε₀ > 0`). For an `ε`-nice instance
with values `u(p, ℓ)ᵢ = (1 + ε)^{v(p,ℓ)ᵢ} aᵢ` and a selection `σ` there is an `ε`-nice count
`c : [d] × [0, b] → ℕ` with (i) `cost(c, i) ≤ (1 + ε) cost(c_σ, i)` for all `i`, (ii) `c ≥ c_σ`,
(iii) `c(i, j) ≤ (n d / ε)^4`. -/
theorem lemma_4_5 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ I : SelInstance, I.Valid → I.IsNice ε →
      ∀ (a : Fin I.d → ℝ) (v : Fin I.n → Fin I.ψ → Fin I.d → ℕ), I.NiceRep ε a v →
      ∀ σ : Fin I.n → Fin I.ψ,
        ∃ c : Fin I.d → ℕ → ℕ, I.IsNiceCount ε c ∧
          (∀ i, I.countCost ε a (fun i j => (c i j : ℝ)) i ≤
            (1 + ε) * I.countCost ε a (fun i j => (I.selCount v σ i j : ℝ)) i) ∧
          (∀ i j, j ≤ I.bb ε → I.selCount v σ i j ≤ c i j) ∧
          (∀ i j, j ≤ I.bb ε → (c i j : ℝ) ≤ ((I.n : ℝ) * I.d / ε) ^ 4) := by sorry

end DistMapClust.Main
