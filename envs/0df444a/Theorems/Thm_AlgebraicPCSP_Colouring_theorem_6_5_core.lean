-- Prove2me | Theorems.Thm_AlgebraicPCSP_Colouring_theorem_6_5_core
-- name    : AlgebraicPCSP.Colouring.theorem_6_5_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:19.290772+00:00
-- url     : https://prove2.me/theorems/b999c604-1368-450d-afd1-6bb72fc2b9c1
-- title:
--   Theorem 6.5 (algebraic core) — Pol(K_k, K_{2k−1}) maps by a minion homomorphism to Pol(H₂, H_K)
-- statement:
--   Let $k \ge 3$. Then there exist $K \ge 2$ and a minion homomorphism
--   $$
--   \xi : \mathrm{Pol}(\mathbf K_k, \mathbf K_{2k-1}) \longrightarrow \mathrm{Pol}(\mathbf H_2, \mathbf H_K),
--   $$
--   where $\mathbf K_c = (E_c; \neq_c)$ is the complete graph on $E_c = \{0, \dots, c-1\}$ and $\mathbf H_K = (E_K; \mathrm{NAE}_K)$ carries the ternary not-all-equal relation.
--
--   This is the algebraic statement through which the paper proves Theorem 6.5, *deciding whether a given graph is $k$-colourable or not even $(2k-1)$-colourable is NP-hard for any $k \ge 3$*: the paper derives Theorem 6.5 from Lemma 6.4 and Corollary 6.3, and the algebraic part of Corollary 6.3 is Theorem 6.2. The minion homomorphism, combined with the reduction theorem (Theorem 3.1) and the NP-hardness of approximate hypergraph colouring (Theorem 5.23, Dinur–Regev–Smyth), yields the hardness.
--
--   **Formalization Note** The NP-hardness conclusion of Theorem 6.5 is not formalized; neither are the log-space reduction of Theorem 3.1 nor the cited Theorem 5.23. The hypothesis $k \ge 3$ is that of Theorem 6.5; with it, $2k - 1$ is computed in $\mathbb N$ without truncation. The codomain is exactly $\mathrm{Pol}(\mathbf H_2, \mathbf H_K)$ with $K \ge 2$; arities $n \ge 1$ throughout.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 39, Theorem 6.5 (algebraic core, via Lemma 6.4 and Theorem 6.2, p. 38)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Colouring_Minion
import Definitions.Def_AlgebraicPCSP_Colouring_Structures

namespace AlgebraicPCSP.Colouring

open PCSPBLPAff.Symmetric

/-- The algebraic core of Theorem 6.5 (arXiv:1811.00970v3, p. 39; the paper deduces Theorem 6.5
from Lemma 6.4 and Corollary 6.3, whose algebraic part is Theorem 6.2): for every `k ≥ 3` there
exist `K ≥ 2` and a minion homomorphism from `Pol(K_k, K_{2k−1})` to `𝓗_K = Pol(H₂, H_K)`.
The NP-hardness conclusion of Theorem 6.5 is not formalized. -/
theorem theorem_6_5_core (k : ℕ) (hk : 3 ≤ k) :
    ∃ (K : ℕ) (hK : 2 ≤ K)
      (ξ : (n : ℕ) → ((Fin n → Fin k) → Fin (2 * k - 1)) → ((Fin n → Fin 2) → Fin K)),
      IsMinionHom (Pol (Kgraph k) (Kgraph (2 * k - 1)) (Kgraph_template (by omega)))
        (HMinion K hK) ξ := by sorry

end AlgebraicPCSP.Colouring
