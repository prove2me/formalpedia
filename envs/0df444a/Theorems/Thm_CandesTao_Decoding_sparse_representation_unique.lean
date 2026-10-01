-- Prove2me | Theorems.Thm_CandesTao_Decoding_sparse_representation_unique
-- name    : CandesTao.Decoding.sparse_representation_unique
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-30T22:11:22.026899+00:00
-- url     : https://prove2.me/theorems/dae66c35-49d1-4d1c-9f30-cfe96740e7c0
-- title:
--   Lemma 1.3: an $S$-sparse representation is unique when $\delta_{2S} < 1$
-- statement:
--   Let $F$ be a real $p \times m$ matrix with columns $v_1, \dots, v_m$, and suppose that $S \ge 1$ is such that $\delta_{2S} < 1$. Let $T$ be a set of at most $S$ indices, let $c$ be an arbitrary real coefficient vector supported on $T$, and put $f := F_T c = \sum_{j \in T} c_j v_j$. Then the set $T$ and the coefficients $(c_j)_{j \in T}$ can be reconstructed uniquely from knowledge of $f$ and the $v_j$: if $c'$ is supported on a set $T'$ with $|T'| \le S$ and
--   $$
--   \sum_{j} c'_j v_j = f ,
--   $$
--   then $c' = c$.
--
--   This is the abstract existence statement behind sparse recovery: under $\delta_{2S} < 1$, an $S$-sparse vector is determined by its image $Fc$. It supplies no efficient algorithm; Theorem 1.4 shows that under the slightly stronger condition (1.10) the linear program $(P_1)$ finds this unique representation.
--
--   **Formalization Note** "The set $T$ and the coefficients can be reconstructed uniquely" is formalized as the statement the paper proves: any two representations of $f$ by coefficient vectors supported on sets of size at most $S$ coincide as vectors of $\mathbb{R}^m$, so the support (the set of nonzero coordinates) is determined as well. The hypothesis $2S \le m$ is the domain of $\delta_{2S}$ in Definition 1.1.
-- source:
--   Candès--Tao 2005, Decoding by Linear Programming, IEEE Trans. Inform. Theory 51(12):4203-4215, doi:10.1109/TIT.2005.858979; arXiv:math/0502327v1 (https://arxiv.org/abs/math/0502327), p. 5, Lemma 1.3 and its proof

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry

namespace CandesTao.Decoding
theorem sparse_representation_unique {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ)
    (hS : 1 ≤ S) (hSm : 2 * S ≤ m) (hδ : restrictedIsometryConst F (2 * S) < 1)
    (T T' : Finset (Fin m)) (hT : T.card ≤ S) (hT' : T'.card ≤ S)
    (c c' : Fin m → ℝ) (hc : SupportedOn c T) (hc' : SupportedOn c' T')
    (hf : F.mulVec c = F.mulVec c') : c = c' := by sorry
end CandesTao.Decoding
