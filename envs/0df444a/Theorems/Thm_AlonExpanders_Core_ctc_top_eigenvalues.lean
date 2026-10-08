-- Prove2me | Theorems.Thm_AlonExpanders_Core_ctc_top_eigenvalues
-- name    : AlonExpanders.Core.ctc_top_eigenvalues
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:09:33.006995+00:00
-- url     : https://prove2.me/theorems/ef3757d5-6f73-43a2-8297-e6fa33ada349
-- title:
--   Proof of Lemma 3.3 — the two largest eigenvalues of $C^TC$ are $d^2$ and $(d-\lambda)^2$
-- statement:
--   Let $G = (I, O; E)$ be a $d$-regular bipartite graph with $|I| = |O| = n \ge 2$, let $\lambda = \lambda(G)$ be the second-smallest eigenvalue of its Laplacian $Q_G = dI - A_G$, and let $C = (c_{io})_{i \in I, o \in O}$ be its binary matrix ($c_{io} = 1$ iff $io \in E$). Let $\mu_1 \ge \mu_2 \ge \dots \ge \mu_n$ be the eigenvalues of the symmetric positive semidefinite $n \times n$ matrix $C^{T}C$, counted with multiplicity. Then
--
--   $$
--   \mu_1 = d^2 \qquad \text{and} \qquad \mu_2 = (d - \lambda)^2 .
--   $$
--
--   This is the spectral input to Tanner's bound in the proof of Lemma 3.3: it expresses the second singular value of $C$ through the Laplacian gap $\lambda(G)$.
--
--   **Formalization Note** $C^TC$ is written `Cᴴ * C`, which over $\mathbb{R}$ is the transpose product, and its eigenvalues are Mathlib's `eigenvalues₀`, listed in decreasing order, so indices $0$ and $1$ are the largest and second largest. The hypothesis $n \ge 2$ is added and necessary: for $n = 1$ the matrix $C^TC$ is $1 \times 1$ and has no second eigenvalue.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 92, proof of Lemma 3.3 ("the two largest eigenvalues of C^T C are d^2 and (d−λ)^2")

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonExpanders_Core_IsIOBipartite
import Definitions.Def_AlonExpanders_Core_biadjMatrix

namespace AlonExpanders.Core

/-- Proof of Lemma 3.3 in Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), p. 92:
for a `d`-regular bipartite graph on `I ⊕ O` with `|I| = |O| = n ≥ 2` and binary matrix `C`, the
two largest eigenvalues of `CᵀC` (counted with multiplicity) are `d²` and `(d − λ(G))²`.
Mathlib's `eigenvalues₀` lists the eigenvalues in decreasing order, so indices `0` and `1` are the
largest and the second largest. Over `ℝ`, `Cᴴ * C = Cᵀ C`. -/
theorem ctc_top_eigenvalues {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ)
    (hI : Fintype.card I = n) (hO : Fintype.card O = n) (hn : 2 ≤ n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) :
    (Matrix.isHermitian_conjTranspose_mul_self (biadjMatrix G)).eigenvalues₀ ⟨0, by omega⟩ =
        (d : ℝ) ^ 2 ∧
      (Matrix.isHermitian_conjTranspose_mul_self (biadjMatrix G)).eigenvalues₀ ⟨1, by omega⟩ =
        ((d : ℝ) - AlonMilman.Diameter.lambda1 G) ^ 2 := by sorry

end AlonExpanders.Core
