-- Prove2me | Theorems.Thm_DirectedOpinion_NoMemory_proposition_3
-- name    : DirectedOpinion.NoMemory.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:27.120978+00:00
-- url     : https://prove2.me/theorems/dfef3f03-f951-48c1-baff-a71183ad0d51
-- title:
--   Proposition 3, pp. 9–10 — on a tree limit, 𝓡* = Σ_s Σ_{l≤s} Σ_{|j|=l} Π_j a_{l,s} 𝓦_j^(s)
-- statement:
--   Consider a rooted tree in Ulam–Harris form with in-degrees $\mathcal N_{\mathbf i}$ and weights $\mathcal C_{(\mathbf i,j)}$, signals $\mathcal W^{(s)}_{\mathbf i}$ ($s\ge0$) at every node, and parameters $c,d$. Let $\Delta$ be the tree operator (10) with self-weight $1-c-d$ and let
--   $$\mathcal R^*=\sum_{s=0}^{\infty}\big(\Delta^s\mathcal W^{(s)}\big)(\emptyset)$$
--   be the stationary opinion of the root. Then
--   $$\mathcal R^*=\sum_{s=0}^{\infty}\sum_{l=0}^{s}\sum_{|\mathbf j|=l}\Pi_{\mathbf j}\,a_{l,s}\,\mathcal W^{(s)}_{\mathbf j},\qquad a_{l,s}=\binom{s}{l}(1-c-d)^{s-l},$$
--   where $\Pi_{\mathbf j}$ is the product of the weights along the path from the root to $\mathbf j$, i.e. $\Pi_{(\mathbf i,j)}=\Pi_{\mathbf i}\mathcal C_{(\mathbf i,j)}$ with $\Pi_\emptyset=1$.
--
--   This explicit series, display (5) of the paper, is the representation of the typical stationary opinion from which all the moment computations of Section 5 start.
--
--   **Formalization Note.** The paper assumes the hypotheses of Theorem 2 with a tree as local limit; the proof (p. 28) uses only that the limit is a tree ("not necessarily a Galton–Watson tree"). The Lean statement holds for every tree, every weight array and every signal array, with $\mathcal R^*$ taken to be $\sum_s(\Delta^s\mathcal W^{(s)})(\emptyset)$, the representation from the proof of Theorem 2 (p. 27); the identification of this series with the limit in distribution of Theorem 2 is not part of this statement. The two series agree term by term in $s$, so no summability hypothesis is involved. Child indices are 0-based.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, pp. 9–10, Proposition 3, display (5)

import Mathlib
import Definitions.Def_DirectedOpinion_NoMemory_Setting
open MeasureTheory ProbabilityTheory

namespace DirectedOpinion.NoMemory

/-- Proposition 3, pp. 9–10: on a tree, 𝓡* = Σ_{s≥0} Σ_{l=0}^s Σ_{|j|=l} Π_j a_{l,s} 𝓦_j^(s), where
𝓡* = Σ_{s≥0} (Δ^s 𝓦^(s))(∅) is `rootOpinion` with self-weight 1 − c − d. Stated for every tree
`n`, every weight array `w` and every signal array `sig`. -/
theorem proposition_3 (n : Label → ℕ) (w : Label → ℕ → ℝ) (c d : ℝ) (sig : ℕ → Label → ℝ) :
    rootOpinion n w (1 - c - d) sig =
      ∑' s : ℕ, ∑ l ∈ Finset.range (s + 1), ∑ t ∈ level n [] l,
        pathW n w [] t * aCoef c d l s * sig s t := by sorry

end DirectedOpinion.NoMemory
