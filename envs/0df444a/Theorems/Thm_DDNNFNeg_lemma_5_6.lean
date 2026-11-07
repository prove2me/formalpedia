-- Prove2me | Theorems.Thm_DDNNFNeg_lemma_5_6
-- name    : DDNNFNeg.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:57.477105+00:00
-- url     : https://prove2.me/theorems/b5b3656e-440e-4e5b-952f-d9e3c22ac98b
-- title:
--   Lemma 5.6 — $\mathbb P[X \in R] \le 2^{-\Omega(n)}$ for every balanced rectangle $R \subseteq f_G^{-1}(0)$
-- statement:
--   Let $\gamma \in (0,1)$. There are $\kappa > 0$ and $n_0$, depending only on $\gamma$, such that for every $n \ge n_0$, every simple 3-regular balanced-cut $\gamma$-edge expander $G$ on $[n]$ with a proper 3-edge-colouring $c$, every balanced partition $(A, B)$ and every rectangle $R \subseteq f_G^{-1}(0)$ with respect to $(A, B)$,
--   $$
--   \mathbb P[X \in R] = \frac{|R \cap I|}{|I|} \le 2^{-\kappa n},
--   $$
--   where $I$ is the set of independent sets of $G$ and $X$ is a uniformly random element of $I$.
--
--   This is the rectangle-size bound that gives the $2^{\Omega(n)}$ lower bound on $\mathrm{Cov}^m_0(f_G)$.
--
--   Differences from the source:
--   - generalization: G as promised by Proposition 5.2, with its fixed γ → every γ ∈ (0,1), with constants depending only on γ; reason: the paper's γ is one instance
--   - reading: 2^{−Ω(n)} → ≤ 2^{−κn} for all n ≥ n₀, with κ > 0 and n₀ depending only on γ; reason: the standard reading of Ω
--   - encoding: P[X ∈ R] for X uniform on independent sets → |R ∩ I| / |I| with I = indepSets G; reason: as written in the proof of Theorem 5.3, p.15
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Lemma 5.6, p.14 (setting p.13)

import Mathlib
import Definitions.Def_DDNNFNeg_fG
import Definitions.Def_DDNNFNeg_IsBalancedCutExpander
import Definitions.Def_DDNNFNeg_IsProperEdgeColoring
import Definitions.Def_DDNNFNeg_IsRectangle
import Definitions.Def_DDNNFNeg_indepSets

namespace DDNNFNeg

/-- **Lemma 5.6** (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.14): let `X` be the indicator vector of a uniformly random independent
set in `G` and `R ⊆ f_G⁻¹(0)` a balanced rectangle, respecting some balanced partition `(A, B)`.
Then `P[X ∈ R] ≤ 2^{−Ω(n)}`.

**Formalization Note** The setting is that of §5.2: `G` a simple 3-regular balanced-cut
`γ`-edge expander on `Fin n` with a proper 3-edge-colouring `c`; the paper fixes one `γ`
(Proposition 5.2), here `γ ∈ (0, 1)` is arbitrary. `P[X ∈ R] = |R ∩ I| / |I|` with `I` the
independent sets (as in the proof of Theorem 5.3, p.15), and `2^{−Ω(n)}` is read as `≤ 2^{−κn}`
for `n ≥ n₀`, with `κ > 0` and `n₀` depending only on `γ`. -/
theorem lemma_5_6 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.IsRegularOfDegree 3 →
      IsBalancedCutExpander γ G → ∀ c : Sym2 (Fin n) → Fin 3, IsProperEdgeColoring G c →
      ∀ A : Finset (Fin n), IsBalanced A → ∀ R : Set (Fin n → Bool), IsRectangle A R →
      (∀ x ∈ R, fG G c x = false) →
      ((R ∩ ↑(indepSets G)).ncard : ℝ) / ((indepSets G).card : ℝ) ≤ (2 : ℝ) ^ (-(κ * n)) := by sorry

end DDNNFNeg
