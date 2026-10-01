-- Prove2me | Theorems.Thm_CandesTao_Decoding_l1_recovers_sparse_vector
-- name    : CandesTao.Decoding.l1_recovers_sparse_vector
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-30T22:26:59.630262+00:00
-- url     : https://prove2.me/theorems/4c4d8f8c-24ac-4e41-a18d-d47557367259
-- title:
--   Theorem 1.4: $\ell^1$ minimization recovers every $S$-sparse vector when $\delta_S + \theta_{S,S} + \theta_{S,2S} < 1$
-- statement:
--   Let $F$ be a real $p \times m$ matrix with columns $v_1, \dots, v_m$, and suppose that $S \ge 1$ is such that
--   $$
--   \delta_S + \theta_{S,S} + \theta_{S,2S} < 1 . \tag{1.10}
--   $$
--   Let $c$ be a real vector supported on a set $T \subseteq \{1, \dots, m\}$ obeying $|T| \le S$, and put $f := Fc$. Then $c$ is the unique minimizer of
--   $$
--   (P_1) \qquad \min_{d \in \mathbb{R}^m} \|d\|_{\ell^1} \quad \text{subject to} \quad Fd = f .
--   $$
--
--   This is the paper's main result: under a deterministic "restricted orthonormality" hypothesis on $F$, far weaker than orthonormality of its columns and compatible with $m$ much larger than $p$, the convex program $(P_1)$, which can be recast as a linear program, recovers every sufficiently sparse vector exactly and with no probability of failure. By Lemma 1.2, condition (1.10) implies $\delta_{2S} < 1$ (the hypothesis of Lemma 1.3) and is implied by $\delta_S + \delta_{2S} + \delta_{3S} < 1$.
--
--   **Formalization Note** "Unique minimizer" means that $c$ is feasible and every other feasible $d$ has strictly larger $\ell^1$ norm. The hypothesis $3S \le m$ is the domain on which Definition 1.1 defines $\theta_{S,2S}$.
-- source:
--   Candès--Tao 2005, Decoding by Linear Programming, IEEE Trans. Inform. Theory 51(12):4203-4215, doi:10.1109/TIT.2005.858979; arXiv:math/0502327v1 (https://arxiv.org/abs/math/0502327), p. 6, Theorem 1.4, condition (1.10); proof in Section 2.2, p. 11

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_CandesTao_Decoding_L1Minimization

namespace CandesTao.Decoding
theorem l1_recovers_sparse_vector {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ)
    (hS : 1 ≤ S) (hSm : 3 * S ≤ m)
    (h : restrictedIsometryConst F S + restrictedOrthogonalityConst F S S +
      restrictedOrthogonalityConst F S (2 * S) < 1)
    (T : Finset (Fin m)) (c : Fin m → ℝ) (hT : T.card ≤ S) (hc : SupportedOn c T) :
    IsUniqueL1Minimizer F (F.mulVec c) c := by sorry
end CandesTao.Decoding
