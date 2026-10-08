-- Prove2me | Theorems.Thm_ConservativeAD_AutoDiff_eq_10
-- name    : ConservativeAD.AutoDiff.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:04.258854+00:00
-- url     : https://prove2.me/theorems/dcb6bfe5-7f35-4d62-9238-eb780bec5f8f
-- title:
--   (10) — $L_k(x)=\{I-e_ke_k^T+e_kd^T : d\in D_k(x)\}$ is a conservative mapping for $G_k$
-- statement:
--   Consider an evaluation program and a non-input node $k$ whose elementary function $g_k$ has a conservative field $D_k$ (Definition 2). Let $G_k:\mathbb R^q\to\mathbb R^q$, $G_k(x)=x+e_k\big(g_k(x_{\mathtt{parents}(k)})-x_k\big)$, and let $\tilde D_k$ be $D_k$ lifted to $\mathbb R^q$ by zeros at the coordinates that are not parents of $k$. Then
--
--   $$
--   L_k: x\mapsto\{I-e_ke_k^T+e_kd^T : d\in\tilde D_k(x)\} \tag{10}
--   $$
--
--   is a conservative mapping for $G_k$.
--
--   In the proof of Theorem 8, each step of Algorithm 1 is rewritten as a map $G_k$ on $\mathbb R^q$, and (10) supplies its generalized Jacobian; the paper derives it from Lemma 3.
--
--   **Formalization Note** Nodes are 0-based. The conclusion is the chain-rule property of Definition 4; local Lipschitz continuity of $G_k$ is not part of it.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 22, §5.2, proof of Theorem 8, eq. (10)

import Mathlib
import Definitions.Def_ConservativeAD_AutoDiff_ConservativeField
import Definitions.Def_ConservativeAD_AutoDiff_ConservativeMap
import Definitions.Def_ConservativeAD_AutoDiff_Program
import Definitions.Def_ConservativeAD_AutoDiff_ProofMatrices

namespace ConservativeAD.AutoDiff

/-- Proof of Theorem 8, (10), p. 22. If `D_k` is a conservative field for the elementary function
`g_k` of a non-input node `k`, then `L_k(x) = { I − e_k e_kᵀ + e_k dᵀ : d ∈ D_k(x) }` (with `D_k`
lifted to `ℝ^q` by zeros) is a conservative mapping for `G_k(x) = x + e_k (g_k(x_{parents(k)}) − x_k)`. -/
theorem eq_10 {p q : ℕ} (P : Program p q) (k : Fin q) (hk : p ≤ k.val)
    (hd : ConservativeAD.GradAE.IsPotential (P.D k) (P.g k)) :
    IsConservativeMap (P.G k) (P.L k) := by sorry

end ConservativeAD.AutoDiff
