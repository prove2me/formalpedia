-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_cond8_iff_evol_eq_potential
-- name    : CasinoCPT.Embedding.cond8_iff_evol_eq_potential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:34.059132+00:00
-- url     : https://prove2.me/theorems/7391a571-5aec-4d50-8f34-b7ab0bfd6b28
-- title:
--   Proof of Theorem 3.1, pp. 48–49 — condition (8) holds iff U^µ_T = U_µ on ℤ
-- statement:
--   Let $T\ge1$ and $\mu\in\mathcal P_0(\mathbb Z)$ with $\mu([-T,T])=1$, and let $U^\mu_t$ be the evolutional functions (6). Then condition (8),
--   $$U_\mu(x)\le\frac{U^\mu_{T-1}(x+1)+U^\mu_{T-1}(x-1)}{2},\qquad x=-(T-2),-(T-4),\dots,T-2,$$
--   holds if and only if
--   $$U^\mu_T(x)=U_\mu(x)\qquad\text{for all }x\in\mathbb Z.$$
--
--   This purely analytic equivalence reduces Theorem 3.1 to Proposition A.3. It is what makes (8) a finite list of explicit constraints on $\mu$, used as the feasible set of the mathematical program in §4.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, pp. 48–49, proof of Theorem 3.1

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 3.1, pp. 48–49: for `T ≥ 1` and `μ ∈ 𝒫₀(ℤ)` with `μ([-T, T]) = 1`,
condition (8) holds if and only if `U^μ_T(x) = U_μ(x)` for every integer `x`. -/
theorem cond8_iff_evol_eq_potential (T : ℕ) (hT : 1 ≤ T) (μ : Measure ℤ) (hμ : InP0Z μ)
    (hsupp : μ (Set.Icc (-(T : ℤ)) T) = 1) :
    Cond8 μ T ↔ ∀ x : ℤ, evol μ T x = potential μ (x : ℝ) := by sorry

end CasinoCPT.Embedding
