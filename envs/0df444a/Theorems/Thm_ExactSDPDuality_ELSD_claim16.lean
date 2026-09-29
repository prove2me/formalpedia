-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_claim16
-- name    : ExactSDPDuality.ELSD.claim16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:19:00.59724+00:00
-- url     : https://prove2.me/theorems/1d3fdfff-0572-4afb-a078-69b89594e6b8
-- title:
--   Claim 16 — if G* + Sₖ is not closed then Sₖ ⊂ Sₖ₊₁ and dim Sₖ < dim Sₖ₊₁
-- statement:
--   Let $Q_0,\dots,Q_m$ be real symmetric $n\times n$ matrices with $0\in G = \{x\mid Q(x)\succeq 0\}$, let $G^*$ be the algebraic polar, and $S_k = Q^*(\mathcal W_k)$ with $S_0 = \{0\}$. Let $0\le k\le m-1$. If $G^* + S_k$ is not closed, then
--   $$S_k\subsetneq S_{k+1}\qquad\text{and}\qquad \dim(S_k) < \dim(S_{k+1}).$$
--
--   Since the dimensions are bounded by $m$, the chain $G^*+S_0\subseteq G^*+S_1\subseteq\cdots$ must become closed by step $m-1$; this is the engine of Theorem 12.
--
--   **Formalization Note** The standing assumption $0\in G$ of §2.4 (p. 142) is a hypothesis. The range $k+1\le m$ is the range on which the paper introduces $S_{k+1}$ and uses the claim (p. 145). $\dim(S_k)$ is the finite rank of the linear span of $S_k$, which equals $S_k$ by Lemma 10(ii).
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 146, Claim 16 (standing assumption 0 ∈ G of §2.4, p. 142; S_k defined on p. 145)

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix Pointwise

namespace ExactSDPDuality.ELSD

/-- Claim 16 (Ramana 1997, p. 146), under the standing assumption `0 ∈ G` of §2.4 and for
`0 ≤ k ≤ m − 1` (the range on which `Sₖ₊₁ = Q*(𝒲ₖ₊₁)` is introduced, p. 145): if `G* + Sₖ` is not
closed, then `Sₖ ⊂ Sₖ₊₁` (strictly) and `dim(Sₖ) < dim(Sₖ₊₁)`. -/
theorem claim16 {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (h0 : (0 : Fin m → ℝ) ∈ feasibleSet Q0 Q) (k : ℕ) (hk : k + 1 ≤ m)
    (hnc : ¬ IsClosed (algPolar Q0 Q + Sset Q0 Q k)) :
    Sset Q0 Q k ⊂ Sset Q0 Q (k + 1) ∧
      Module.finrank ℝ (Submodule.span ℝ (Sset Q0 Q k)) <
        Module.finrank ℝ (Submodule.span ℝ (Sset Q0 Q (k + 1))) := by sorry

end ExactSDPDuality.ELSD
