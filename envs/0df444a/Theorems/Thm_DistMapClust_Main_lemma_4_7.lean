-- Prove2me | Theorems.Thm_DistMapClust_Main_lemma_4_7
-- name    : DistMapClust.Main.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:05:49.911924+00:00
-- url     : https://prove2.me/theorems/775b57da-1666-41be-b4c4-58fe921f9394
-- title:
--   Lemma 4.7 — for an ε-nice count dominating c_σ there is an ε-nice selection with respect to it
-- statement:
--   Let $I=(P,U,W,f')$ be an $\varepsilon$-nice instance of Row-Wise Ordered Norm Mapping Selection, $\varepsilon>0$ sufficiently small, with values $u(p,\ell)_i=(1+\varepsilon)^{v(p,\ell)_i}a_i$, let $\sigma$ be a mapping selection and $c:[d]\times[0,b]\to\mathbb N$ an $\varepsilon$-nice count with $c\ge c_\sigma$. Then there is a selection $\sigma'$ that is $\varepsilon$-nice with respect to $c$:
--   $$c_{\sigma'}\le(1+\varepsilon)c\quad\text{and}\quad \nexists\,p,\ell:\ \min_i c(i,v(p,\ell)_i)\ge\min_{i'}c(i',v(p,\sigma'(p))_{i'})\cdot\tfrac{db}{\varepsilon}.$$
--   Together with Lemma 4.5 it lets the dynamic program discard, for each point, every choice that is much worse in all rows.
--
--   **Formalization Note.** $\varepsilon_0$ is universal; $c\ge c_\sigma$ is required on $[d]\times[0,b]$.
--
--   Differences from the source:
--   - reading: §4: 'We always assume ε > 0 to be sufficiently small' → there is a universal ε₀ > 0 such that the statement holds for every ε ∈ (0, ε₀); reason: the standing assumption of §4 (p. 46), with the threshold independent of the instance
--   - reading: v(p, ℓ) with u(p, ℓ)_i = (1 + ε)^{v(p,ℓ)_i} a_i, under the standing assumption 'we assume that u(p, ℓ)_i is always different from ∞' (p. 47) → hypothesis NiceRep ε a v: a ≥ 0 and every value equals ofReal((1 + ε)^{v p ℓ i} · a i) with v p ℓ i ∈ [b/2, b]; the statement is for every such (a, v); reason: v is defined only for finite values; a ≥ 0 because values are nonnegative reals; when a_i > 0 the exponents are unique
--   - encoding: index sets [k], [d], [ψ], [n] (1-based) → Fin k, Fin d, Fin ψ, Fin n (0-based); P an injective family Fin n → α; reason: Lean convention; same instances
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 49, Lemma 4.7

import Mathlib
import Definitions.Def_DistMapClust_Main_Selection

namespace DistMapClust.Main

/-- Lemma 4.7 (p. 49), for `ε` sufficiently small (a universal `ε₀ > 0`). For an `ε`-nice instance
with values `u(p, ℓ)ᵢ = (1 + ε)^{v(p,ℓ)ᵢ} aᵢ`, a selection `σ` and an `ε`-nice count `c ≥ c_σ`, there
is an `ε`-nice selection `σ'` with respect to `c`. -/
theorem lemma_4_7 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ I : SelInstance, I.Valid → I.IsNice ε →
      ∀ (a : Fin I.d → ℝ) (v : Fin I.n → Fin I.ψ → Fin I.d → ℕ), I.NiceRep ε a v →
      ∀ (σ : Fin I.n → Fin I.ψ) (c : Fin I.d → ℕ → ℕ), I.IsNiceCount ε c →
        (∀ i j, j ≤ I.bb ε → I.selCount v σ i j ≤ c i j) →
        ∃ σ' : Fin I.n → Fin I.ψ, I.IsNiceSelection ε v c σ' := by sorry

end DistMapClust.Main
